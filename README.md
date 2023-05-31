# Rum

An embeddable, Lua-inspired Lisp language.

## Example

```txt

; Objects
(def-type! vec3 (x y z))

(set (meta-table vec3) :typedoc
    (make-table
        { :x => num
          :y => num
          :z => num }))

; Meta-tables 
(set (meta-table vec3) :call
    (lambda! (a b c) (new! vec3 '(a b c))))

(def-component! :position vec3)

(def-system! :render
    (and
        (has :position)
        (has :sprite))
    (lambda! (entity)
        (render (get entity :sprite)
                (get entity :position))))

(with! { zero => 0 } [zero zero zero])

(def-obj! "Player"
    (make-component :position (vec3 (0 0 0)))
    (make-component :sprite `$res/path/to/script.png`))

(def-fn! add (a b) (+ a b))

; Match expressions
(match! "foo"
    {
        0 => "Literal zero"
        [] => "Empty"
        [0] => "One zero"
        [_] => "One thing"
        [0 _ 1] => "Zero something one"
        [0 ...] => "Zero then things"
        [...] => "Some array"
        _ => "Anything else" })

; Value literals
(#True #False #FooBar)

; Metaprogramming
(eval ('add 'a 'b))
```

## Philosophy

 * Functions ending in `!` are macros, and don't have their arguments evaluated.
 * All native callbacks are executed via the `call` interface, but typically have
   convenient wrapper functions defined
 * All interpreter state is stored in tables accessible from Rum.
 * Data types are also tables with metaprotocol facilities, also accessible from Rum.

Language Types:
 * List
 * Map
 * Number
 * Path
 * Placeholder
 * String
 * Symbol
 * Value
 * Vector

VM Types:
 * Boolean
 * Function
 * List
 * Number
 * String
 * Symbol
 * Table
 * Unbound
 * Vector
