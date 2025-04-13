import LeanSlides

#slides Introduction /-!
% Lean Slides
% https://github.com/0art0/lean-slides/
% Today

# About

`Lean Slides` is a tool to
automatically generate `reveal.js` slides
from Markdown comments in the Lean editor.

# Use cases

`Lean Slides` can be used in
tutorials or demonstrations
to avoid switching between
the slides and the Lean editor.
-/

-- Some intervening Lean code
example : 1 = 1 := by
  rfl

#slides Tool /-!
# Dependencies

`Lean Slides` works by combining together several tools:

- [`reveal.js`](https://revealjs.com/)

- [`pandoc`](https://pandoc.org/)

- [`node.js`](https://nodejs.org/en)

- [`http-server`](https://www.npmjs.com/package/http-server)

# Usage

To use `Lean Slides`, first install all the dependencies
and start the HTTP server with the command
```lean
lake run lean-slides/serve-slides
```

---

In any file that imports `Lean Slides`, type

```lean
#slides +draft Test /-!
  <Markdown text>
-/
```

# Features

`Lean Slides` turns comments written in the above format
into `reveal.js` slides which are rendered in the infoview
as a [`Widget`](https://github.com/EdAyers/ProofWidgets4).

The tool also features a code action to
go in and out of draft mode.
-/

-- Some more intervening Lean code
#check Nat.succ

#slides +draft Math /-!
# Rendering math

The generated `reveal.js` slides
render mathematics by default
using $\KaTeX$.

-/

#set_pandoc_options "-V" "theme=white"

#slides Options /-!
# A test for pandoc options.

This should use the white theme.
-/
