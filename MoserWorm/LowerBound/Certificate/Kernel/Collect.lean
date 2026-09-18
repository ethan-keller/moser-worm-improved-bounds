import MoserWorm.LowerBound.Certificate.Kernel.Center

/-! Four-bucket coefficient collection with the reference interval bound. -/

namespace MoserWorm.LowerBound.Certificate.Kernel

private theorem intervalAdd_assoc (a b c : DIval) :
    (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp [DIval.add, Int.add_assoc]

private theorem intervalAdd_comm (a b : DIval) : a.add b = b.add a := by
  cases a; cases b
  simp [DIval.add, Int.add_comm]

private theorem filter_insert (f : List Coordinate → Bool) (s : List Coordinate)
    (a : DIval) (p : IPoly Coordinate) :
    (insertCoefficient DIval.add s a p).filter (fun t => f t.1) =
      if f s then insertCoefficient DIval.add s a (p.filter (fun t => f t.1))
      else p.filter (fun t => f t.1) := by
  induction p with
  | nil => cases hs : f s <;> simp [insertCoefficient, hs]
  | cons t p ih =>
    rcases t with ⟨t, b⟩
    by_cases h : s = t
    · subst t
      cases hs : f s <;> simp [insertCoefficient, hs]
    · cases hs : f s <;> cases ht : f t <;>
        simp [insertCoefficient, h, hs, ht, ih]

private theorem filter_collect (f : List Coordinate → Bool) (p : IPoly Coordinate) :
    (collect p).filter (fun t => f t.1) = collect (p.filter (fun t => f t.1)) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨s, a⟩
    change (insertCoefficient DIval.add s a (collect p)).filter _ = _
    rw [filter_insert, ih]
    cases hs : f s <;> simp [hs, collect, collectCoefficients]

private theorem range_filter (f : List Coordinate → Bool) (p : IPoly Coordinate) :
    unitRange p = (unitRange (p.filter (fun t => f t.1))).add
      (unitRange (p.filter (fun t => !f t.1))) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨s, a⟩
    cases hs : f s
    · simp only [List.filter_cons, hs, Bool.false_eq_true, if_false,
        Bool.not_false, if_true]
      rw [unitRange, unitRange, ih]
      rw [← intervalAdd_assoc, intervalAdd_comm _ (unitRange (p.filter fun t => f t.1)),
        intervalAdd_assoc]
    · simp only [List.filter_cons, hs, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [unitRange, unitRange, ih, intervalAdd_assoc]

private theorem range_collect_partition (f : List Coordinate → Bool)
    (p : IPoly Coordinate) :
    unitRange (collect p) =
      (unitRange (collect (p.partition (fun t => f t.1)).1)).add
      (unitRange (collect (p.partition (fun t => f t.1)).2)) := by
  rw [List.partition_eq_filter_filter]
  have h := range_filter f (collect p)
  rw [filter_collect f, filter_collect (fun s => !f s)] at h
  simpa only [Function.comp_def] using h

/-- A bucket selector, not a monomial encoding: collisions remain in the bucket. -/
def bucketCode : List Coordinate → Nat
  | [] => 0
  | [i] => i.2.val + 1
  | _ :: j :: _ => j.2.val + 1

/-- Partition before collecting. The original collector handles every bucket,
including collisions and monomials of arbitrary degree. -/
def bucketRange : Nat → IPoly Coordinate → DIval
  | 0, p => unitRange (collect p)
  | _ + 1, [] => DIval.ofInt 0
  | n + 1, p =>
    let q := p.partition (fun t => (bucketCode t.1).testBit n)
    (bucketRange n q.1).add (bucketRange n q.2)

theorem bucketRange_eq (n : Nat) (p : IPoly Coordinate) :
    bucketRange n p = unitRange (collect p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons t p =>
      simp only [bucketRange, ih]
      exact (range_collect_partition (fun s => (bucketCode s).testBit n) (t :: p)).symm

/-- Four buckets shorten repeated coefficient scans without changing rounding. -/
def bound (p : IPoly Coordinate) (box : Coordinate → DIval) : DIval :=
  bucketRange 2 (sortSupports (fun i j => coordinateCode i ≤ coordinateCode j)
    (center p box))

theorem bound_eq (p : IPoly Coordinate) (box : Coordinate → DIval) :
    bound p box = centeredBound p box := by
  simp only [bound, bucketRange_eq, centeredBound, center_eq]

end MoserWorm.LowerBound.Certificate.Kernel
