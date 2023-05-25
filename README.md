# Rum

A minimal scripting language and command runner.

## Example

```txt
# hello.rum



```

```sh
# myprogram.sh

echo "== Arguments =="
echo $0

echo "== Environment =="
env

echo "== STDIN =="
cat <&0
```

```sh
# Run the program
rum myprogram.sh --config hello.rum
```

```txt
== Arguments ==
hello --world myprogram.sh

== Environment ==
PATH=/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin

== STDIN ==
Hello world!
```
