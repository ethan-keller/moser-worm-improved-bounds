import MoserWorm.Common.Interval.Basic

/-! Sparse interval polynomials. Evaluation uses no real arithmetic or corner enumeration. -/

namespace MoserWorm.LowerBound.Certificate

abbrev SparsePolynomial (ι R : Type) := List (List ι × R)

abbrev IPoly (ι : Type) := SparsePolynomial ι DIval

namespace IPoly

def constant {ι : Type} (a : DIval) : IPoly ι := [([], a)]

def coord {ι : Type} (i : ι) : IPoly ι := [([i], DIval.ofInt 1)]

def add {ι : Type} (p q : IPoly ι) : IPoly ι := p ++ q

def sum {ι : Type} (ps : List (IPoly ι)) : IPoly ι := ps.flatten

def scale {ι : Type} (a : DIval) (p : IPoly ι) : IPoly ι :=
  p.map fun t => (t.1, a.mul t.2)

/-- Repeated variables are retained; sound squarefree use requires disjoint supports. -/
def mul {ι : Type} (p q : IPoly ι) : IPoly ι :=
  p.flatMap fun t => q.map fun u => (t.1 ++ u.1, t.2.mul u.2)

def reindex {ι κ : Type} (f : ι → κ) (p : IPoly ι) : IPoly κ :=
  p.map fun t => (t.1.map f, t.2)

end IPoly

/-- Structural recursion keeps sorting reducible by the kernel. -/
def insertSupport {ι : Type} (le : ι → ι → Bool) (i : ι) : List ι → List ι
  | [] => [i]
  | j :: js => if le i j then i :: j :: js else j :: insertSupport le i js

def sortSupport {ι : Type} (le : ι → ι → Bool) : List ι → List ι
  | [] => []
  | i :: is => insertSupport le i (sortSupport le is)

/-- Canonical support order permits collection across different multiplication orders. -/
def sortSupports {ι : Type} (le : ι → ι → Bool) (p : IPoly ι) : IPoly ι :=
  p.map fun t => (sortSupport le t.1, t.2)

def evalMonomial {ι : Type} (box : ι → DIval) : List ι → DIval
  | [] => DIval.ofInt 1
  | i :: is => (box i).mul (evalMonomial box is)

def evalBox {ι : Type} (p : IPoly ι) (box : ι → DIval) : DIval :=
  match p with
  | [] => DIval.ofInt 0
  | (s, a) :: p => (a.mul (evalMonomial box s)).add (evalBox p box)

/-- Combine equal support lists. Lists in different orders remain separate. -/
def insertCoefficient {ι R : Type} [DecidableEq ι]
    (add : R → R → R) (s : List ι) (a : R) :
    SparsePolynomial ι R → SparsePolynomial ι R
  | [] => [(s, a)]
  | (t, b) :: p =>
      if s = t then (t, add a b) :: p
      else (t, b) :: insertCoefficient add s a p

def collectCoefficients {ι R : Type} [DecidableEq ι]
    (add : R → R → R) : SparsePolynomial ι R → SparsePolynomial ι R
  | [] => []
  | (s, a) :: p => insertCoefficient add s a (collectCoefficients add p)

def collect {ι : Type} [DecidableEq ι] (p : IPoly ι) : IPoly ι :=
  collectCoefficients DIval.add p

/-- Collect coefficients before interval evaluation to retain algebraic cancellation. -/
def bound {ι : Type} [DecidableEq ι] (p : IPoly ι) (box : ι → DIval) : DIval :=
  evalBox (collect p) box

end MoserWorm.LowerBound.Certificate
