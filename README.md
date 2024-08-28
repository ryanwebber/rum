# Rum

An embeddable, Lua-inspired Lisp language where interpreter state is exposed
through meta-table facilities.

## Example

```txt
; Functional
(map [1 2 3] (lambda! (x) (+ x 1)))

; Meta-programming
(set (#meta :locals) "myvar" 42)
(+ myvar 1)

```
