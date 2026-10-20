module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.outMapu2081_comp_inMapu2080
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.outMapu2080_comp_inMapu2081
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.which_inMapu2080_le_trueElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.which_bot_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.outMapu2080_bot_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.outMapu2081_bot_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.which_inMapu2081_le_falseElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.TD_trichotomy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_sumToProdT

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`sumToProdT ∘ condSum ≤ I`.** Case-split `t : T` into `⊥ / true / false`
(`TD_trichotomy`); `condSum(t,x,y)` reduces to a concrete sum element (`⊥`, `in₀ x`, or `in₁ y`)
whose image under `sumToProdT` is read off via the round-trips
`outMap₀_comp_inMap₀`/`outMap₁_comp_inMap₀` (and their mirror images) together with the tag bounds
`which_inMap₀_le_trueElt`/`which_inMap₁_le_falseElt`. -/
theorem sumToProdT_comp_condSum_le :
    (sumToProdT hE).comp (condSum E E hE hE) ≤ idMap (prod TD (prod E E)) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z, ← pair_fst_snd z.snd]
  set t := z.fst; set x := z.snd.fst; set y := z.snd.snd
  clear_value t x y
  rw [toElementMap_comp, toElementMap_idMap]
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [condSum_bot, toElementMap_sumToProdT]
    exact pair_le_pair_iff.mpr ⟨which_bot_le,
      pair_le_pair_iff.mpr ⟨outMap₀_bot_le.trans (E.bot_le x), outMap₁_bot_le.trans (E.bot_le y)⟩⟩
  · rw [condSum_true, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₀_le_trueElt x, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₀_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₁_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
  · rw [condSum_false, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₁_le_falseElt y, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₀_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₁_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le

end Sum
end DomainTheory.NeighbourhoodSystems
