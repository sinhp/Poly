namespace Foo

def bar : Nat := 0

def baz : Nat := 1

end Foo


-- #check bar -- fails because `bar` is not in the root namespace

section annonymous1

#check Foo.bar

#check Foo.baz

#check Foo.Odd

#check Foo.Odd.val

-- or first open `Foo` in this section and then access `bar` and `baz` in it

open Foo

#check bar

#check baz

end annonymous1





section annonymous2

-- open `Foo` but only access `bar` in it
open Foo (bar)

#check bar -- works

#check baz -- fails

end annonymous2


section annonymous3

open Foo hiding bar

#check bar -- fails

#check baz -- works

#check Foo.Odd.val


end annonymous3


section annonymous4

open Foo in
#check bar

-- #check baz -- fails because `Foo` was opened only for `bar`.

end annonymous4


namespace Foo

-- introducing a new namespace `Qux` inside `Foo`

namespace Qux

def quux : Nat := 2

end Qux

end Foo

#check Foo.Qux.quux


section annonymous5

--#check Foo.quux -- fails because `quux` is in `Foo.Qux` namespace

open Foo.Qux

#check quux

end annonymous5
