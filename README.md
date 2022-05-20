# nuMonitor

First of all, you need to load nuMonitor.pl in SWI-Prolog.

To use the script exploiting syntactic encoding:
```bash
?- LTL = <your_LTL_formula>, monitor6(syntactic, LTL, <Alphabet>, <Trace>, Verdict).
```

To use the script exploiting sematic encoding:
```bash
?- LTL = <your_LTL_formula>, monitor6(semantic, LTL, <Alphabet>, <Trace>, Verdict).
```

The Verdict variable is unified with the monitor's verdict.

## Examples

### Eventually p
```bash
?- LTL = eventually(prop(p,tt)), monitor6(syntactic, LTL, [p,q,s], [[q], [q,s]], Verdict).
```
Expected result: Verdict = ?(tt)

```bash
?- LTL = eventually(prop(p,tt)), monitor6(semantic, LTL, [p,q,s], [[q], [q,s]], Verdict).
```
Expected result: Verdict = ?(tt)

```bash
?- LTL = eventually(prop(p,tt)), monitor6(syntactic, LTL, [p,q,s], [[q], [q,s], [p]], Verdict).
```
Expected result: Verdict = tt

```bash
?- LTL = eventually(prop(p,tt)), monitor6(semantic, LTL, [p,q,s], [[q], [q,s], [p]], Verdict).
```
Expected result: Verdict = tt

### Globally p

```bash
?- LTL = globally(prop(p,tt)), monitor6(syntactic, LTL, [p,q,s], [[p,q], [p]], Verdict).
```
Expected result: Verdict = ?(ff)

```bash
?- LTL = globally(prop(p,tt)), monitor6(semantic, LTL, [p,q,s], [[p,q], [p]], Verdict).
```
Expected result: Verdict = ?(ff)

```bash
?- LTL = globally(prop(p,tt)), monitor6(syntactic, LTL, [p,q,s], [[p,q], [p], [q]], Verdict).
```
Expected result: Verdict = ff

```bash
?- LTL = globally(prop(p,tt)), monitor6(semantic, LTL, [p,q,s], [[p,q], [p], [q]], Verdict).
```
Expected result: Verdict = ff

### Non-monitorable (E.g. globally eventually p)

```bash
?- LTL = globally(eventually(prop(p,tt))), monitor6(syntactic, LTL, [p,q,s], [[p,q], [p], [q]], Verdict).
```
Expected result: Verdict = x

```bash
?- LTL = globally(eventually(prop(p,tt))), monitor6(semantic, LTL, [p,q,s], [[p,q], [p], [q]], Verdict).
```
Expected result: Verdict = x

### Counterexample showing that Syntactic encoding is not the best approximation (this causes the syntactic monitor to lose anticipation)

```bash
?- LTL = globally(eventually(prop(p,tt))), monitor6(semantic, LTL, [p,q,s], [[p,q], [p], [q]], Verdict).
```
Expected result: Verdict = ?(ff)

```bash
?- LTL = until(prop(p,tt), ff), monitor6(semantic, LTL, [p,q,s], [[p]], Verdict).
```
Expected result: Verdict = ff


