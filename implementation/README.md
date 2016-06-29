# Disjoint Intersection Types

## Build and Run

This project can be built with `cabal` or `stack`.

* cabal
```
cabal sandbox init
cabal install --only-dependencies
cabal build
cabal exec disjoint-intersection-exe
```

* stack
```
stack build
stack exec disjoint-intersection-exe
```

## REPL

The REPL prompt is `>`, type `:q` to quit or input any expression in the source language to check its result.

```
> 2 : int

Abstract syntax
Anno (IntV 2) IntT

Pretty printing
2 : int

Source typing result
int

Target expression after translation
2

Target typing result
int

Target evaluation result
2
```

## Syntax of the source langauge

* Primitive type: `int`, `bool`
* Top type/value: `T : T`
* Type annotation: `2 : int`
* Lambda: `(\x . x+1) : int->int`
* Pair: `(1, true)`
* Projection: `(1, true)._1`, `(1, true)._2`
* Merge: `true ,, (\x.x) : int->int`
* Intersection type: `bool & (int->int)`
* Let: `let x = 3 in (x, x + 1)`
* If: `if x == 0 then true else false`

## Examples

```
let x = (3,,true) in let succ = (\x.x+1):int->int in let not = (\x.if x then false else true):bool->bool in (succ x, not x)

Target typing result
(int, bool)

Target evaluation result
(4, False)
```

```
let succ = (\x.x+1):int->int in ((1,,true) ,, (2,,false))

Source typing result
(int & bool) and (int & bool) are not disjoint
```

```
let succ = (\x.x+1):int->int in let not = (\x.if x then false else true):bool->bool in ((succ,,not):int->int) (3,,true)

Target typing result
int

Target evaluation result
4
```

```
((\f . f (3,,true)) : ((int & bool) -> T) -> T) ((\x.x) : int->int ,, (\x.x) : bool -> bool)

Target typing result
()

Target evaluation result
()
```
