module

public import DomainTheory.DataTypesAsLattices.Lambda.sequences
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def dollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (seqShift u)) (predSet z))

namespace dollarStepBody

theorem isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => dollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (seqShift u))
      (funOf.isScottContinuous_left (predSet z))
      (funOf.isScottContinuous_left (seqShift u))
  exact theorem_1_3 (condSet.isScottContinuous_right z (funOf u (ofNat 0))) hinner

theorem isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => dollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (seqShift u))
      (funOf.isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf.isScottContinuous s) seqShift.left_isScottContinuous)
  exact theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_mid z y)
    (fun x => condSet.isScottContinuous_right z x)
    (funOf.isScottContinuous_left (ofNat 0)) helse

theorem isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => dollarStepBody s u z) :=
  theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet.isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf.isScottContinuous (funOf s (seqShift u)))
      predSet.isScottContinuous)

end dollarStepBody

def dollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => dollarStepBody s u z))

namespace dollarStep

theorem isScottContinuous : IsScottContinuous dollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => dollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => dollarStepBody s u z)
      (fun z => dollarStepBody.isScottContinuous_s u z))

theorem app (s u : Pomega) :
    funOf (dollarStep s) u = graph (fun z => dollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => dollarStepBody s u z)
    (fun z => dollarStepBody.isScottContinuous_u s z)) u

theorem app2 (s u z : Pomega) :
    funOf (funOf (dollarStep s) u) z = dollarStepBody s u z := by
  rw [dollarStep.app]
  exact beta (dollarStepBody.isScottContinuous_z s u) z

theorem iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot dollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf.bot, seqFunLt.zero]
  | succ n ih =>
    rw [iterateBot, dollarStep.app2, dollarStepBody, ih, seqFunLt.succ]

theorem fix_app (u z : Pomega) :
    funOf (funOf (fix dollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix dollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot dollarStep n) u) z := by
    simp [fix, funOf.iUnion]
  rw [this, seqFun.eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep.iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep.iterate] using hn⟩

end dollarStep

def termDollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (termShift u)) (predSet z))

namespace termDollarStepBody

theorem isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => termDollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (termShift u))
      (funOf.isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf.isScottContinuous s) termShift.left_isScottContinuous)
  exact theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_mid z y)
    (fun x => condSet.isScottContinuous_right z x)
    (funOf.isScottContinuous_left (ofNat 0)) helse

theorem isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => termDollarStepBody s u z) :=
  theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet.isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf.isScottContinuous (funOf s (termShift u)))
      predSet.isScottContinuous)

theorem isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => termDollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (termShift u))
      (funOf.isScottContinuous_left (predSet z))
      (funOf.isScottContinuous_left (termShift u))
  exact theorem_1_3 (condSet.isScottContinuous_right z (funOf u (ofNat 0))) hinner

end termDollarStepBody

def termDollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => termDollarStepBody s u z))

namespace termDollarStep

theorem isScottContinuous : IsScottContinuous termDollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => termDollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => termDollarStepBody s u z)
      (fun z => termDollarStepBody.isScottContinuous_s u z))

theorem app (s u : Pomega) :
    funOf (termDollarStep s) u = graph (fun z => termDollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => termDollarStepBody s u z)
    (fun z => termDollarStepBody.isScottContinuous_u s z)) u

theorem app2 (s u z : Pomega) :
    funOf (funOf (termDollarStep s) u) z = termDollarStepBody s u z := by
  rw [app]
  exact beta (termDollarStepBody.isScottContinuous_z s u) z

theorem iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot termDollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf.bot, seqFunLt.zero]
  | succ n ih =>
    rw [iterateBot, app2, termDollarStepBody, ih, seqFunLt.term]

theorem fix_app (u z : Pomega) :
    funOf (funOf (fix termDollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix termDollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot termDollarStep n) u) z := by
    simp [fix, funOf.iUnion]
  rw [this, seqFun.eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [iterate] using hn⟩

end termDollarStep

def dollarStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 2)
      (.app (.var 1) .zero)
      (.app (.app (.var 0) (.lam 3 (.app (.var 1) (.succ (.var 3)))))
        (.pred (.var 2))))))

namespace dollarStepTerm

theorem interp :
    interp dollarStepTerm (fun _ => botElem) = graph termDollarStep := by
  unfold dollarStepTerm termDollarStep termDollarStepBody termShift DomainTheory.DataTypesAsLattices.interp
  apply congrArg graph
  funext s
  simp only[envSet]
  apply congrArg graph
  funext u
  simp only[envSet]
  apply congrArg graph
  funext z
  simp[envSet, condSet, succSet]
  rfl

end dollarStepTerm

def dollarC : Pomega :=
  graph (fun u => graph (fun x => seqFun u x))

namespace dollarC
theorem app (u : Pomega) :
    funOf dollarC u = graph (fun x => seqFun u x) :=
  beta (graph_const_isScottContinuous (fun u x => seqFun u x)
    (fun x => seqFun.left_isScottContinuous x)) u

theorem eq_fix_termDollarStep : dollarC = fix termDollarStep := by
  have hfix : termDollarStep (fix termDollarStep) = fix termDollarStep :=
    (theorem_1_4 termDollarStep.isScottContinuous).1
  have hbody : ∀ u z, termDollarStepBody (fix termDollarStep) u z = seqFun u z := by
    intro u z
    calc termDollarStepBody (fix termDollarStep) u z
        = funOf (funOf (termDollarStep (fix termDollarStep)) u) z :=
          (termDollarStep.app2 _ _ _).symm
      _ = funOf (funOf (fix termDollarStep) u) z := by rw [hfix]
      _ = seqFun u z := termDollarStep.fix_app u z
  have : termDollarStep (fix termDollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

theorem combinatory : IsCombinatory dollarC := by
  have hY : funOf Ycomb (interp dollarStepTerm (fun _ => botElem)) = dollarC := by
    rw [dollarStepTerm.interp, theorem_2_5 termDollarStep.isScottContinuous,
      dollarC.eq_fix_termDollarStep]
  exact hY ▸ IsCombinatory.app Ycomb.combinatory (theorem_2_4.closed dollarStepTerm)

end dollarC

theorem eq_2_24 (u x : Pomega) :
    seqFun u x =
      condSet x (funOf u (ofNat 0))
        (seqFun (seqShift u) (predSet x)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift.app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      simpa [this] using hki
  · intro hk
    rcases hk with ⟨hk0, h0x⟩ | ⟨hpos, t, ht⟩
    · exact Set.mem_iUnion₂.mpr ⟨0, h0x, hk0⟩
    · obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hpos
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift.app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      refine Set.mem_iUnion₂.mpr ⟨i + 1, hi, ?_⟩
      simpa [this] using hki

namespace eq_2_24

theorem Y : dollarC = fix dollarStep := by
  have hfix : dollarStep (fix dollarStep) = fix dollarStep :=
    (theorem_1_4 dollarStep.isScottContinuous).1
  have hbody : ∀ u z, dollarStepBody (fix dollarStep) u z = seqFun u z := by
    intro u z
    calc dollarStepBody (fix dollarStep) u z
        = funOf (funOf (dollarStep (fix dollarStep)) u) z :=
          (dollarStep.app2 _ _ _).symm
      _ = funOf (funOf (fix dollarStep) u) z := by rw [hfix]
      _ = seqFun u z := dollarStep.fix_app u z
  have : dollarStep (fix dollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

theorem Ycomb : funOf Ycomb (graph dollarStep) = dollarC := by
  rw [theorem_2_5 dollarStep.isScottContinuous, eq_2_24.Y]

end eq_2_24

theorem eq_2_25 (u x : Pomega) :
    funOf (funOf dollarC u) x = seqFun u x := by
  rw [dollarC.app]
  exact beta (seqFun.right_isScottContinuous u) x

def lamOmega (τ : ℕ → Pomega) : Pomega :=
  funOf dollarC (graph (fun z => ⋃ n ∈ z, τ n))

end DomainTheory.DataTypesAsLattices
