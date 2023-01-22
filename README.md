# subsumes
Relational term subsumption for SWI-Prolog

`subsumes/2` is intended as a relational drop-in replacement for [`subsumes_term/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes_term/2). It can handle cyclic data, as well as cases where cyclic data would be induced.

```prolog
?- f(X, Y) subsumes G.
G = f(_A, _B),
X subsumes _A,
Y subsumes _B.

?- f(X) subsumes Y, Y subsumes X. % Example with induced cyclic data.
X = Y, Y = f(Y).

?- X subsumes Y, X = g(_).
X = g(_A),
Y = g(_B),
_A subsumes _B.
```

See the unit tests in [`test/subsumes.plt`](test/subsumes.plt) for more examples.

Executing the following goal from the top-level `subsumes` directory should run all the tests:
```prolog
?- expand_file_name("test/**.plt", Tests), maplist(consult, Tests), run_tests.
```

Note that this conflicts with the deprecated [`terms:subsumes/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes/2).

TODO: make ISO-compatible.

(Note to self) To publish a new version:
1. update `pack.pl`
2. do GitHub release with new tag matching the pack.pl version
3. execute:
```prolog
?- make_directory(potato), pack_install(subsumes, [url('http://github.com/GeoffChurch/subsumes/archive/13.17.zip'), package_directory(potato)]).
```