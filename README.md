[Proofs Verified with Lean4 (leanprover/lean4:v4.8.0-rc1)](https://github.com/sinhp/LeanHomotopyFrobenius/blob/master/lean-toolchain)

# Lean4 Formalization Of Polynomial Functors

This repository is a [Lean 4](https://github.com/leanprover/lean4) formalization of the theory of Polynomial Functors. Polynomial Functors categorify polynomial functions.

## Acknowledgment
The work has been done during the Trimester Program "Prospects of formal mathematics" at the Hausdorff Institute (HIM) in Bonn.

## Content (under development)

As part of this formalization, we also formalize locally cartesian closed categories in Lean4.

- [x] Locally cartesian closed categories
  - [x] The Beck-Chevalley condition in LCCC
  - [x] LCCC structure on types
  - [x] LCCC structure on presheaves of types

- [ ] Univariate Polynomial Functors
  - [x] Definition of univariate polynomial functors
  - [x] The construction of associated polynomial functors
  - [x] Monomials
  - [x] Linear polynomials
  - [x] Sums of polynomials
  - [ ] Products of polynomials
  - [x] Composition of polynomials
  - [x] The classifying property of polynomial functors
  - [x] The monoidal category `C [X]` of univariate polynomial functors
  - [ ] The bicategory of polynomial functors
  - [ ] Cartesian closedness of a category of polynomial functors

- [ ] Multivariate Polynomial Functors
  - [x] Definition of multivariate polynomial functors
  - [x] The construction of associated polynomial functors
  - [x] Monomials
  - [x] Linear polynomials
  - [ ] Sums of polynomials
  - [ ] Products of polynomials
  - [ ] Composition of polynomials
  - [ ] The classifying property of polynomial functors
  - [ ] The bicategory of multivariate polynomial functors
  - [ ] The double category of polynomial functors

- [ ] Polynomial functors and the semantics of linear logic
  - [ ] A relational presentation of polynomial functors
  - [ ] The differential calculus of polynomials

- [ ] Polynomial functors and generalized combinatorial species

### Resources

# Main references used in the formalization

> - [Wellfounded Trees and Dependent Polynomial Functors, Nicola Gambino⋆ and Martin Hyland](https://www.dpmms.cam.ac.uk/~martin/Research/Publications/2004/gh04.pdf)
> - [Tutorial on Polynomial Functors and Type Theory, Steve Awodey](https://www.cmu.edu/dietrich/philosophy/hott/slides/polytutorial.pdf)
> - [Polynomial functors and polynomial monads, Nicola Gambino and Joachim Kock](https://arxiv.org/abs/0906.4931)
> - [Notes on Locally Cartesian Closed Categories, Sina Hazratpour](https://sinhp.github.io/files/CT/notes_on_lcccs.pdf)
> - [Notes on Polynomial Functors, Joachim Kock](https://mat.uab.cat/~kock/cat/polynomial.pdf)

## Additional references on polynomial functors

> Nicola Gambino, Martin Hyland. Wellfounded trees and dependent polynomial functors.  Types for proofs and programs. International workshop, TYPES 2003, Torino, Italy, 2003. Revised selected papers. Springer Berlin, 2004. p. 210-225.

> Nicola Gambino and Joachim Kock. Polynomial functors and polynomial monads. Mathematical Proceedings of the Cambridge Philosophical Society, 154(1):153–192, 2013.

> Joachim Kock. Data types with symmetries and polynomial functors over groupoids. Electronic Notes in Theoretical Computer Science, 286:351–365, 2012. Proceedings of the 28th Conference on the Mathematical Foundations of Programming Semantics (MFPS XXVIII).

> Paul-André Melliès. Template games and differential linear logic. Proceedings of the 34th Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'19.

> Marcelo Fiore, Nicola Gambino, Martin Hyland, and Glynn Winskel. The cartesian closed bicategory of generalised species of structures. J. Lond. Math. Soc. (2), 77(1):203–220, 2008.

> Tamara Von Glehn. Polynomials and models of type theory. PhD thesis, University of Cambridge, 2015.

> E. Finster, S. Mimram, M. Lucas, T. Seiller. A Cartesian Bicategory of Polynomial Functors in Homotopy Type Theory, MFPS 2021.  https://arxiv.org/pdf/2112.14050.

> Jean-Yves Girard. Normal functors, power series and λ-calculus. Ann. Pure Appl. Logic, 37(2):129–177, 1988. doi:10.1016/0168-0072(88)90025-5.

> Mark Weber (2015): Polynomials in categories with pullbacks. Theory and applications of categories 30(16), pp. 533–598.

> David Gepner, Rune Haugseng, and Joachim Kock. 8-Operads as analytic monads. International Mathematics Research Notices, 2021.

> Steve Awodey and Clive Newstead. Polynomial pseudomonads and dependent type theory, 2018.

> Steve Awodey, Natural models of homotopy type theory, Mathematical Structures in Computer Science, 28 2 (2016) 241-286, arXiv:1406.3219.

> Sean K. Moss and Tamara von Glehn. Dialectica models of type theory, LICS 2018.

> Thorsten Altenkirch, Neil Ghani, Peter Hancock, Conor McBride, Peter Morris. Indexed containers. Journal of Functional Programming 25, 2015.

> Jakob Vidmar (2018): Polynomial functors and W-types for groupoids. Ph.D. thesis, University of Leeds.
