%%% @private
-module(concuerror_instrumenter).

-export([instrument/3]).

-define(inspect, concuerror_inspect).

-define(flag(A), (1 bsl A)).

-define(input, ?flag(1)).
-define(output, ?flag(2)).

-define(ACTIVE_FLAGS, [?input, ?output]).

-define(DEBUG_FLAGS, lists:foldl(fun erlang:'bor'/2, 0, ?ACTIVE_FLAGS)).
-include("concuerror.hrl").

-spec instrument(module(), erl_syntax:forms(), concuerror_loader:instrumented())
                -> {erl_syntax:forms(), [iodata()]}.

instrument(?inspect, AbstractCode, _Instrumented) ->
  %% The inspect module should never be instrumented.
  {AbstractCode, []};
instrument(Module, AbstractCode, Instrumented) ->
  ?if_debug(Stripper = fun(Node) -> erl_syntax:set_ann(Node, []) end),
  ?debug_flag(?input, "~s~n",
              [[erl_prettypr:format(erl_syntax_lib:map(Stripper, A))
                || A <- AbstractCode]]),
  true = ets:insert(Instrumented, {{current}, Module}),
  Acc =
    #{ file => ""
     , instrumented => Instrumented
     , warnings => []
     },
  {Is, #{warnings := Warnings}} = fold(AbstractCode, Acc, []),
  true = ets:delete(Instrumented, {current}),
  ?debug_flag(?output, "~s~n",
              [[erl_prettypr:format(erl_syntax_lib:map(Stripper, I))
                || I <- Is]]),
  {Is, warn_to_string(Module, lists:usort(Warnings))}.

%% Replace with form_list please.
fold([], Arg, Acc) ->
  {erl_syntax:revert_forms(lists:reverse(Acc)), Arg};
fold([H|T], Arg, Acc) ->
  ArgIn = Arg#{var => erl_syntax_lib:variables(H)},
  {R, NewArg} = erl_syntax_lib:mapfold(fun mapfold/2, ArgIn, H),
  fold(T, NewArg, [R|Acc]).

mapfold(Node, Acc) ->
  #{ file := File
   , instrumented := Instrumented
   , warnings := Warnings
   } = Acc,
  Type = erl_syntax:type(Node),
  NewNodeAndMaybeWarn =
    case Type of
      application ->
        Args = erl_syntax:application_arguments(Node),
        LArgs = erl_syntax:list(Args),
        Op = erl_syntax:application_operator(Node),
        OpType = erl_syntax:type(Op),
        case OpType of
          module_qualifier ->
            Module = erl_syntax:module_qualifier_argument(Op),
            Name = erl_syntax:module_qualifier_body(Op),
            case is_safe(Module, Name, length(Args), Instrumented) of
              has_load_nif -> {warn, Node, has_load_nif};
              true -> Node;
              false ->
                inspect(call, [Module, Name, LArgs], Node, Acc)
            end;
          atom -> Node;
          _ ->
            io:format("THIS: ~p~n", [{OpType, Node}]),
            inspect(apply, [Op, LArgs], Node, Acc)
        end;
      infix_expr ->
        Op = erl_syntax:infix_expr_operator(Node),
        COp = erl_syntax:operator_name(Op),
        case COp of
          '!' ->
            Left = erl_syntax:infix_expr_left(Node),
            Right = erl_syntax:infix_expr_right(Node),
            Args = erl_syntax:list([Left, Right]),
            inspect(call, [abstr(erlang), abstr(send), Args], Node, Acc);
          _ -> Node
        end;
      receive_expr ->
        Node;
      _ -> Node
    end,
  {NewNode, NewWarnings} =
    case NewNodeAndMaybeWarn of
      {warn, NT, W} -> {NT, [W|Warnings]};
      _ -> {NewNodeAndMaybeWarn, Warnings}
    end,
  NewFile =
    case Type of
      attribute ->
        case erl_syntax_lib:analyze_attribute(Node) of
          {file, {NF, _}} -> NF;
          _ -> File
        end;
      _ -> File
    end,
  NewAcc =
    Acc
    #{ file => NewFile
     , warnings => NewWarnings
     },
  {NewNode, NewAcc}.


%% mapfold(Tree, {Instrumented, Var, Warnings}) ->
%%   Type = cerl:type(Tree),
%%   NewTreeAndMaybeWarn =
%%     case Type of
%%       apply ->
%%         Op = cerl:apply_op(Tree),
%%         case cerl:is_c_fname(Op) of
%%           true -> Tree;
%%           false ->
%%             OldArgs = cerl:make_list(cerl:apply_args(Tree)),
%%             inspect(apply, [Op, OldArgs], Tree)
%%         end;
%%       call ->
%%         Module = cerl:call_module(Tree),
%%         Name = cerl:call_name(Tree),
%%         Args = cerl:call_args(Tree),
%%         case is_safe(Module, Name, length(Args), Instrumented) of
%%           has_load_nif -> {warn, Tree, has_load_nif};
%%           true -> Tree;
%%           false ->
%%             inspect(call, [Module, Name, cerl:make_list(Args)], Tree)
%%         end;
%%       'receive' ->
%%         Clauses = cerl:receive_clauses(Tree),
%%         Timeout = cerl:receive_timeout(Tree),
%%         Action = cerl:receive_action(Tree),
%%         Fun = receive_matching_fun(Tree),
%%         Call = inspect('receive', [Fun, Timeout], Tree),
%%         case Timeout =:= cerl:c_atom(infinity) of
%%           false ->
%%             %% Replace original timeout with a fresh variable to make it
%%             %% skippable on demand.
%%             TimeoutVar = cerl:c_var(Var),
%%             RecTree = cerl:update_c_receive(Tree, Clauses, TimeoutVar, Action),
%%             cerl:update_tree(Tree, 'let', [[TimeoutVar], [Call], [RecTree]]);
%%           true ->
%%             %% Leave infinity timeouts unaffected, as the default code generated
%%             %% by the compiler does not bind any additional variables in the
%%             %% after clause.
%%             cerl:update_tree(Tree, seq, [[Call], [Tree]])
%%         end;
%%       _ -> Tree
%%     end,
%%   {NewTree, NewWarnings} =
%%     case NewTreeAndMaybeWarn of
%%       {warn, NT, W} -> {NT, [W|Warnings]};
%%       _ -> {NewTreeAndMaybeWarn, Warnings}
%%     end,
%%   NewVar =
%%     case Type of
%%       'receive' -> Var + 1;
%%       _ -> Var
%%     end,
%%   {NewTree, {Instrumented, NewVar, NewWarnings}}.

inspect(Tag, Args, Node, Acc) ->
  #{ file := File} = Acc,
  Pos = erl_syntax:get_pos(Node),
  PosInfo = [Pos, {file, File}],
  CTag = abstr(Tag),
  CArgs = erl_syntax:list(Args),
  App =
    erl_syntax:application( abstr(?inspect)
                          , abstr(inspect)
                          , [ CTag
                            , CArgs
                            , abstr(PosInfo)]),
  erl_syntax:copy_attrs(Node, App).

%% receive_matching_fun(Tree) ->
%%   Msg = cerl:c_var(message),
%%   Clauses = extract_patterns(cerl:receive_clauses(Tree)),
%%   Body = cerl:update_tree(Tree, 'case', [[Msg], Clauses]),
%%   cerl:update_tree(Tree, 'fun', [[Msg], [Body]]).

%% extract_patterns(Clauses) ->
%%   extract_patterns(Clauses, []).

%% extract_patterns([], Acc) ->
%%   Pat = [cerl:c_var(message)],
%%   Guard = cerl:c_atom(true),
%%   Body = cerl:c_atom(false),
%%   lists:reverse([cerl:c_clause(Pat, Guard, Body)|Acc]);
%% extract_patterns([Tree|Rest], Acc) ->
%%   Body = cerl:c_atom(true),
%%   Pats = cerl:clause_pats(Tree),
%%   Guard = cerl:clause_guard(Tree),
%%   extract_patterns(Rest, [cerl:update_c_clause(Tree, Pats, Guard, Body)|Acc]).

is_safe(Module, Name, Arity, Instrumented) ->
  case
    erl_syntax:is_literal(Module) andalso
    erl_syntax:is_literal(Name)
  of
    false -> false;
    true ->
      NameLit = concr(Name),
      ModuleLit = concr(Module),
      case {ModuleLit, NameLit, Arity} of
        %% erlang:apply/3 is safe only when called inside of erlang.erl
        {erlang, apply, 3} ->
          ets:lookup_element(Instrumented, {current}, 2) =:= erlang;
        {erlang, load_nif, 2} ->
          has_load_nif;
        _ ->
          case erlang:is_builtin(ModuleLit, NameLit, Arity) of
            true ->
              not concuerror_callback:is_unsafe({ModuleLit, NameLit, Arity});
            false ->
              ets:lookup(Instrumented, ModuleLit) =/= []
          end
      end
  end.

abstr(Term) ->
  erl_syntax:abstract(Term).

concr(Tree) ->
  erl_syntax:concrete(Tree).

warn_to_string(Module, Tags) ->
  [io_lib:format("Module ~w ~s", [Module, tag_to_warn(T)]) || T <- Tags].

%%------------------------------------------------------------------------------

tag_to_warn(has_load_nif) ->
  "contains a call to erlang:load_nif/2."
    " Concuerror cannot reliably execute operations that are implemented as"
    " NIFs."
    " Moreover, Concuerror cannot even detect if a NIF is used by the test."
    " If your test uses NIFs, you may see error messages of the form"
    " 'replaying a built-in returned a different result than expected'."
    " If your test does not use NIFs you have nothing to worry about.".
