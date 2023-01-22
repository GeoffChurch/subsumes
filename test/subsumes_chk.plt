:- use_module("../prolog/subsumes").

:- begin_tests(subsumes_chk).

test(incomparable_terms) :-
    \+ subsumes_chk(f, g).

test(identical_terms) :-
    subsumes_chk(f(X,Y), f(X,Y)).

test(variant_terms) :-
    \+ subsumes_chk(f(_), f(_)).

test(vars) :-
    G subsumes S,
    subsumes_chk(G, S).

test(cyclic_nonsubsuming) :-
    A = f(A, _),
    \+ subsumes_chk(A, f(A, _)).

test(cyclic_subsuming) :-
    A = f(A, _),
    A subsumes B,
    subsumes_chk(A, B).

test(permavar_subsumes_anything) :-
    X subsumes 1,
    X subsumes 2,
    subsumes_chk(X, 3).

:- end_tests(subsumes_chk).

%%% UTILS %%%

get_lbs(G, LBs) :- get_attr(G, subsumes, LBs), !.
get_lbs(_, []).

check_lbs(G, Expected) :-
    get_lbs(G, Actual),
    msort(Expected, X),
    msort(Actual, X).
