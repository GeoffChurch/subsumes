# subsumes
Relational term subsumption for SWI-Prolog

`subsumes/2` is intended as a relational drop-in replacement for the anyway deprecated [`terms:subsumes/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes/2). It can handle cyclic data, as well as cases where cyclic data would be induced.

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

## Installation in SWI-Prolog

```prolog
?- pack_install(subsumes).
```

## Testing

Executing the following goal from the top-level `subsumes` directory should run all the tests:
```prolog
?- expand_file_name("test/*.plt", Tests), maplist(consult, Tests), run_tests.
```

---

TODO: make ISO-compatible.

(Note to self) To publish a new version:
1. update `pack.pl`
2. do GitHub release with new tag matching the pack.pl version
3. execute:
```bash
swipl -g "make_directory(temp), pack_install(subsumes, [url('https://github.com/GeoffChurch/subsumes/archive/0.5.zip'), pack_directory(temp), interactive(false)]), delete_directory_and_contents(temp)" -t halt
```
