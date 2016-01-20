-module(fact_main).
-export([fact/1]).

fact(N) ->
    FactorialActor = spawn(fun() -> factorial:factorial_behv({tt}) end),
    FactorialActor ! {tuple_msg, {nat_msg, int2nat(N)}, {name_msg, self()}},
    receive
        {nat_msg, Result} ->
            io:fwrite("fact(~w) = ~w~n", [N, nat2int(Result)]);
        _ ->
            io:fwrite("error~n")
    end.

nat2int({o}) -> 0;
nat2int({s, N}) -> nat2int(N) + 1.

int2nat(0) -> {o};
int2nat(N) when N > 0 -> {s, int2nat(N - 1)};
int2nat(_) -> {o}.
