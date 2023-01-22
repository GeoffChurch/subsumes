:- module(subsumes, [
	      subsumes/2,
	      op(700, xfx, subsumes),
	      subsumes_chk/2
	  ]).

:- consult(guardedmap).

%!  subsumes(?General, ?Specific) is semidet.
%
%   subsumes/2 maintains the relation that one term subsumes another,
%   according to standard unification of terms.
%
%   See the unit tests for examples.
subsumes(General, Specific) :-
    guardedmap(
        guard,
        subsumes_,
        [General, Specific]).

subsumes_(General, Specific) :-
    var(General)
    ->  add_lb(General, Specific)
    ;   subsumes_var(General, Specific).

%!  subsumes_chk(+General, +Specific) is semidet.
%
%   Holds if `General` necessarily subsumes `Specific`.
%   This predicate fails to be relational when subsumption is induced after it fails:
%   ==
%   ?- \+ subsumes_chk(G, S), G subsumes S, subsumes_chk(G, S).
%   G subsumes S.
%   ==
subsumes_chk(General, Specific) :-
    guardedmap(
	guard,
	subsumes_chk_,
	[General, Specific]).

subsumes_chk_(General, Specific) :- General == Specific, !.
subsumes_chk_(General, _) :- permavar(General), !.
subsumes_chk_(General, Specific) :-
    get_lbs(General, LBs),
    member(LB, LBs),
    subsumes_chk(LB, Specific).

guard(General, Specific) :- var(General) ; var(Specific).

subsumes_var(G, S) :-
    term_variables(G, GVars),
    (any(subsumes_chk(S), GVars)
    ->  % S already subsumes some var in G, so G subsumes S implies S = G.
        % This avoids nontermination when subsumption would induce cyclic
        % data, e.g. `f(X) subsumes Y, Y subsumes X`.
        S = G
    ;   copy_term_nat(G, S),
        term_variables(S, SVars),
        GVars subsumes SVars).

% Add a lower bound to G.
add_lb(G, LB) :-
    collapse_cycle(G, LB)
    ->  true
    ;   get_lbs(G, LBs),
        set_lbs(G, [LB|LBs]),
        compact_lbs(G).

% Collapse all paths from Cur to End, or fail if no path exists.
collapse_cycle(End, Cur) :-
    End == Cur
    ->  true
    ;   get_lbs(Cur, CurLBs),
        set_lbs(Cur, []),
        % If collapse_cycle(End, LB) doesn't succeed on any LBs, then fail
        % because there are no cycles. Otherwise, replace its current LBs
        % with just the LBs which didn't cycle.
        partition(collapse_cycle(End), CurLBs, [_|_], RemainingLBs),
        Cur = End, % Cur has no LBs so this doesn't risk repeating work via attr_unify_hook.
        call_dcg((get_lbs, append(RemainingLBs)), End, LBs),
        set_lbs(Cur, LBs),
        compact_lbs(Cur).

% WARNING: This only works assuming G is var, while the expected behavior
% might be that `get_lbs(G, LBs)` is equivalent to `get_lbs(G, LBs), maplist(subsumes(G), LBs)`.
get_lbs(G, LBs) :- get_attr(G, subsumes, LBs), !.
get_lbs(_, []).

% WARNING: This only works assuming G is var, while the expected behavior
% might be that `set_lbs(G, LBs)` is equivalent to `set_lbs(G, LBs), maplist(subsumes(G), LBs)`.
set_lbs(G, []) :- !, del_attr(G, subsumes).
set_lbs(G, LBs) :- put_attr(G, subsumes, LBs).

% compact_lbs(G) just de-dupes G's lower bounds, and removes any self-subsumption. It doesn't merge LBs or remove redundant transitive subsumptions.
compact_lbs(G) :-
    permavar(G)
    ->  true
    ;   % Consider merging mergeable LBs, and maybe mark dummy variables in their attributes.
        call_dcg((get_lbs, sort, ignore(selectchk_eq(G))), G, LBs),
        set_lbs(G, LBs).

%!  permavar(+V) is semidet.
%
%   Succeeds if the set of terms subsumed by `V` contains a pair of nonvars
%   with a var LGG. If so, `var(V)` must always hold. This is equivalent
%   to e.g. `subsumes_chk(G, apple), subsumes_chk(G, orange)`.
permavar(V) :-
    call_dcg((get_lbs, include(nonvar), foldl1(term_subsumer)), V, LGG),
    var(LGG),
    % The following is just an optimization in case LBs is large.
    set_lbs(V, [every, thing]).

attr_unify_hook(LBs, Y) :- maplist(subsumes(Y), LBs).

attribute_goals(G) -->
    { compact_lbs(G),
      get_lbs(G, LBs),
      attribute_goals_(LBs, G, Goals) },
    Goals.

attribute_goals_([],  _, []) :- !.
attribute_goals_([S], G, [G subsumes S]) :- !.
attribute_goals_(LBs, G, [maplist(subsumes(G), LBs)]).

%%% UTILS %%%

foldl1(Goal, [V0|List], V) :-
    foldl(Goal, List, V0, V).

member_eq(A, Bs) :-
    member(B, Bs),
    A == B,
    !.

ignore(G) --> G, !.
ignore(_) --> [].

%!  selectchk_eq(+Elem)// is semidet.
%
%   Removes the first occurrence of Elem. Equality is tested with ==.
selectchk_eq(X) --> [Y], { X == Y }, !.
selectchk_eq(X), [Y] --> [Y], selectchk_eq(X).

any(G, Xs) :-
    member(X, Xs),
    call(G, X).
