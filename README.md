[Proofs Verified with Lean4 (leanprover/lean4:v4.8.0-rc1)](https://github.com/sinhp/LeanHomotopyFrobenius/blob/master/lean-toolchain)

# Lean4 Formalization Of Polynomial Functors

This repository is a [Lean 4](https://github.com/leanprover/lean4) formalization of the theory of Polynomial Functors. Polynomial Functors categorify 
polynomials. 

## Acknowledgment 
The work has been done during the Trimester Program "Prospects of formal mathematics" at the Hausdorff Institute (HIM) in Bonn. 

## Content (under development)

As part of this formalization, we also formalize locally cartesian closed categories in Lean4. 

- [ ] Polynomial functors as endofunctors on the category of types
  - [x] Definition of univariate polynomials as a type family
  - [x] The construction of a bundle map associated to a polynomial 
  - [x] The construction of associated polynomial functor
  - [ ] Definition of multivariate polynomials and the associated polynomial functor
  - [x] Monomials 
  - [x] Linear polynomials
  - [x] Sums of polynomials
  - [ ] Products of polynomials
  - [x] Composition of polynomials
  - [ ] The classifying property of polynomial functors
  - [ ] The category `Type [X]` of polynomial functors in one variable
  - [ ] Differential calculus of polynomials
- [ ] Polynomial functors in locally cartesian closed categories
    - [x] Definition of locally cartesian closed category
    - [ ] Beck-Chevalley condition in LCCCs
    - [x] Polynomial functors in LCCCs
    - [ ] The bicategory of polynomial functors 
    - [ ] Cartesian closedness of a category of polynomial functors

- [x] The LCCC structure on presheaves of types
  - [ ] Polynomial endofunctors on presheaves of types
  - [ ] CwFs as cocontinuous polynomials
- [ ] Polynomials as models of intuitionistic linear logic
- [ ] Generalized combinatorial species

### Resources 

# Some references

> - [Wellfounded Trees and Dependent Polynomial Functors, Nicola Gambino⋆ and Martin Hyland](https://www.dpmms.cam.ac.uk/~martin/Research/Publications/2004/gh04.pdf)
> - [Tutorial on Polynomial Functors and Type Theory, Steve Awodey](https://www.cmu.edu/dietrich/philosophy/hott/slides/polytutorial.pdf)
> - [Polynomial functors and polynomial monads, Nicola Gambino and Joachim Kock](https://arxiv.org/abs/0906.4931)
> - [Notes on Locally Cartesian Closed Categories, Sina Hazratpour](https://sinhp.github.io/files/CT/notes_on_lcccs.pdf)
> - [Notes on Polynomial Functors, Joachim Kock](https://mat.uab.cat/~kock/cat/polynomial.pdf)

> 1. Wellfounded trees and dependent polynomial functors.Gambino, Nicola; Hyland, Martin. Types for proofs and programs. International workshop, TYPES 2003, Torino, Italy, 2003. Revised selected papers.. Springer Berlin, 2004. p. 210-225.

> 2. Tamara Von Glehn. Polynomials and models of type theory. PhD thesis, University of Cambridge, 2015.

> 3. Joachim Kock. Data types with symmetries and polynomial functors over groupoids. Electronic Notes in Theoretical Computer Science, 286:351–365, 2012. Proceedings of the 28th Conference on the Mathematical Foundations of Programming Semantics (MFPS XXVIII).

> 4. Jean-Yves Girard. Normal functors, power series and λ-calculus. Ann. Pure Appl. Logic, 37(2):129–177, 1988. doi:10.1016/0168-0072(88)90025-5.

> 5. David Gepner, Rune Haugseng, and Joachim Kock. 8-Operads as analytic monads. Interna- tional Mathematics Research Notices, 2021.

> 6. Nicola Gambino and Joachim Kock. Polynomial functors and polynomial monads. Mathematical Proceedings of the Cambridge Philosophical Society, 154(1):153–192, 2013.

> 7. Marcelo Fiore, Nicola Gambino, Martin Hyland, and Glynn Winskel. The cartesian closed bicategory of generalised species of structures. J. Lond. Math. Soc. (2), 77(1):203–220, 2008.

> 8. M. Fiore, N. Gambino, M. Hyland, and G. Winskel. Relative pseudomonads, Kleisli bicategories, and substitution monoidal structures. Selecta Mathematica, 24(3):2791–2830, 2018.

> 9. Steve Awodey and Clive Newstead. Polynomial pseudomonads and dependent type theory, 2018.

> 10. Steve Awodey, Natural models of homotopy type theory, Mathematical Structures in Computer Science, 28 2 (2016) 241-286, arXiv:1406.3219.

> 11. Sean K. Moss and Tamara von Glehn. Dialectica models of type theory, LICS 2018. 



