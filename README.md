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
> _ [Wellfounded Trees and Dependent Polynomial Functors, Nicola Gambino⋆ and Martin Hyland](https://www.dpmms.cam.ac.uk/~martin/Research/Publications/2004/gh04.pdf)
> - [Tutorial on Polynomial Functors and Type Theory, Steve Awodey](https://www.cmu.edu/dietrich/philosophy/hott/slides/polytutorial.pdf)
> - [Polynomial functors and polynomial monads, Nicola Gambino and Joachim Kock](https://arxiv.org/abs/0906.4931)
> - [Notes on Locally Cartesian Closed Categories, Sina Hazratpour](https://sinhp.github.io/files/CT/notes_on_lcccs.pdf)
> - [Notes on Polynomial Functors, Joachim Kock](https://mat.uab.cat/~kock/cat/polynomial.pdf)





