:- use_module("../prolog/subsumes").

:- begin_tests(subsumes).

test(direct_unresolvable_subsumption_fails) :-
    \+ f subsumes g.

test(indirect_unresolvable_subsumption_fails) :-
    X subsumes f,
    X subsumes g,
    \+ g subsumes X.

test(idempotent) :-
    maplist(subsumes(X), [f(g),f(g),A,B,A]),
    check_lbs(X, [A,B,f(g)]).

test(multiple_cycles_collapsed) :-
    X = [A,B,C,A,D],
    Y = [B,C,E,D,E],
    maplist([V]>>(V subsumes f(V)), X),
    X subsumes Y,
    % Now induce cycle with two distinct paths: A-B-C-E and A-D-E.
    E subsumes A,
    % Make sure both paths were collapsed.
    maplist(==(A), [B,C,D,E]),
    check_lbs(A, [f(A)]).

test(compact_lbs_compacts_permavar) :-
    maplist(subsumes(X), [1, 2, 3, 4, 5, 6]),
    compact_lbs(X),
    check_lbs(X, [every, thing]).

test(permavar_preserves_lbs) :-
    subsumes(G, a),
    subsumes(G, b),
    check_lbs(G, [a, b]).

test(goal_residuation) :-
    subsumes(U, a),
    copy_term(U, U_, UGoals),
    assertion(UGoals == [subsumes:subsumes(U_, a)]),
    subsumes(G, a),
    subsumes(G, b),
    copy_term(G, G_, GGoals),
    assertion(GGoals == [maplist(subsumes:subsumes(G_), [a, b])]).

test(compact_lbs_keeps_non_permavar_bounds) :-
    subsumes(U, L),
    compact_lbs(U),
    check_lbs(U, [L]).

test(compact_lbs_dedups) :-
    subsumes(G, f(X)),
    subsumes(G, f(Y)),
    X = Y,
    check_lbs(G, [f(X), f(Y)]),
    compact_lbs(G),
    check_lbs(G, [f(X)]).

test(is_permavar_true) :-
    subsumes(G, a),
    subsumes(G, b),
    is_permavar(G).

test(is_permavar_false_single_subsumption) :-
    subsumes(G, a),
    \+ is_permavar(G).

test(is_permavar_false_fresh) :-
    \+ is_permavar(_).

test(is_permavar_false_nonvar) :-
    \+ is_permavar(foo).

test(subsumption_with_directly_induced_cyclic_data_terminates) :-
    f(X, Y) subsumes X,
    X == f(X, Y).

test(subsumption_with_1_step_indirectly_induced_cyclic_data_terminates2) :-
    f(X) subsumes Y,
    Y subsumes X.

test(subsumption_with_2_step_indirectly_induced_cyclic_data_terminates) :-
    X subsumes Y,
    Y subsumes Z,
    X = f(Z).

test(subsumption_with_cyclic_data) :-
    X = f(X, Y),
    X subsumes f(f(A, B), C),
    term_variables(A, [Fresh]),
    A == f(A, Fresh),    
    check_lbs(Y, [C, B, Fresh]).

test(subsume_then_unify_leaves_loop) :-
    X subsumes Y,
    X = Y,
    % This is unfortunate but unavoidable, as attr_unify_hook is not called
    % when unifying with an unattributed variable. However, it is unobservable
    % because dedup_lbs/1 is called by attribute_goals//1.
    check_lbs(X, [X]).

%%% UTILS %%%

get_lbs(G, LBs) :- get_attr(G, subsumes, LBs), !.
get_lbs(_, []).

check_lbs(G, Expected) :-
    get_lbs(G, Actual),
    assertion(Actual == Expected).

:- end_tests(subsumes).
