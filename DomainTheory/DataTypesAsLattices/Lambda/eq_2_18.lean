module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.minExtend
public import DomainTheory.DataTypesAsLattices.Lambda.maxExtend
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Occurs
public import DomainTheory.DataTypesAsLattices.Lambda.rename
public import DomainTheory.DataTypesAsLattices.Lambda.curry2
public import DomainTheory.DataTypesAsLattices.Lambda.curry3
public import DomainTheory.DataTypesAsLattices.Lambda.ScottContinuousFin
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin
public import DomainTheory.DataTypesAsLattices.Lambda.nestApplyFin
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.seq0
public import DomainTheory.DataTypesAsLattices.Lambda.seq1
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.relComp
public import DomainTheory.DataTypesAsLattices.Lambda.setSum
public import DomainTheory.DataTypesAsLattices.Lambda.topRec
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.abs
public import DomainTheory.DataTypesAsLattices.Lambda.erase
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Lambda.seqCons
public import DomainTheory.DataTypesAsLattices.Lambda.interStep
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt
public import DomainTheory.DataTypesAsLattices.Lambda.lamOmega
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal
public import DomainTheory.DataTypesAsLattices.Lambda.primRecHat
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep
public import DomainTheory.DataTypesAsLattices.Lambda.Ymap
public import DomainTheory.DataTypesAsLattices.Lambda.Fofg
public import DomainTheory.DataTypesAsLattices.Lambda.Yterm
public import DomainTheory.DataTypesAsLattices.Lambda.termShift
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_18_bot
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_18_top
public import DomainTheory.DataTypesAsLattices.Lambda.pair_eq_right
public import DomainTheory.DataTypesAsLattices.Lambda.exists_least_not_mem
public import DomainTheory.DataTypesAsLattices.Lambda.exists_least_mem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.18).** `a = λx. a` iff `a = ⊥` or `a = ⊤`. -/
theorem eq_2_18 (a : Pomega) :
    a = graph (fun _ => a) ↔ a = botElem ∨ a = topElem := by
  constructor
  · intro ha
    by_cases htop : a = topElem
    · exact Or.inr htop
    · have hex : ∃ k, k ∉ a := by
        by_contra h
        apply htop
        ext k
        constructor
        · intro; trivial
        · intro
          exact not_not.mp (not_exists.mp h k)
      obtain ⟨k, hk, hmin⟩ := exists_least_not_mem hex
      obtain ⟨n, m, hnm⟩ := exists_pair k
      have hm : m ∉ a := by
        intro hma
        have : pair n m ∈ a :=
          ha.symm ▸ (⟨n, m, rfl, hma⟩ : pair n m ∈ graph (fun _ => a))
        exact hk (by rwa [hnm] at this)
      have : m = k :=
        le_antisymm (by rw [← hnm]; exact pair_le_right n m)
          (le_of_not_gt fun hlt => hm (hmin m hlt))
      have hnmk : pair n k = k := by simpa [this] using hnm
      have ⟨_, hk0⟩ := pair_eq_right hnmk
      have h0 : 0 ∉ a := by simpa [hk0] using hk
      by_cases hbot : a = botElem
      · exact Or.inl hbot
      · obtain ⟨l, hl, hlmin⟩ := exists_least_mem (Set.nonempty_iff_ne_empty.mpr hbot)
        obtain ⟨i, j, hij⟩ := exists_pair l
        have hj : j ∈ a := by
          have : pair i j ∈ graph (fun _ => a) :=
            ha ▸ (by rwa [hij] : pair i j ∈ a)
          rcases this with ⟨i', j', hp, hj'⟩
          obtain ⟨rfl, rfl⟩ := pair_inj hp
          exact hj'
        have : j = l :=
          le_antisymm (by rw [← hij]; exact pair_le_right i j)
            (le_of_not_gt fun hlt => hlmin j hlt hj)
        have hil : pair i l = l := by simpa [this] using hij
        have ⟨_, hl0⟩ := pair_eq_right hil
        exact (h0 (by simpa [hl0] using hl)).elim
  · intro h
    rcases h with rfl | rfl
    · exact eq_2_18_bot
    · exact eq_2_18_top

end DomainTheory.DataTypesAsLattices
