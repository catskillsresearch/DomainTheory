module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_s
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_u
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_z
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_bot
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_zero
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_succ_term
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_iUnion
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_eq_iUnion_lt

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def termDollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => termDollarStepBody s u z))

namespace termDollarStep

theorem isScottContinuous : IsScottContinuous termDollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => termDollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => termDollarStepBody s u z)
      (fun z => termDollarStepBody_isScottContinuous_s u z))

theorem app (s u : Pomega) :
    funOf (termDollarStep s) u = graph (fun z => termDollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => termDollarStepBody s u z)
    (fun z => termDollarStepBody_isScottContinuous_u s z)) u

theorem app2 (s u z : Pomega) :
    funOf (funOf (termDollarStep s) u) z = termDollarStepBody s u z := by
  rw [app]
  exact beta (termDollarStepBody_isScottContinuous_z s u) z

theorem iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot termDollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, app2, termDollarStepBody, ih, seqFunLt_succ_term]

theorem fix_app (u z : Pomega) :
    funOf (funOf (fix termDollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix termDollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot termDollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [iterate] using hn⟩

end termDollarStep

end DomainTheory.DataTypesAsLattices
