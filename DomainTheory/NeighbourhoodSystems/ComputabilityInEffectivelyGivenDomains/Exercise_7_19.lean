module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powerFunctor

@[expose] public section

open DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Exercise 7.19: powerdomain functoriality of PFmap. -/
theorem example_719 :
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (f : ApproximableMap V W),
      (PFmapComb V W).toElementMap (toFilter f) = toFilter (PFmap f)) ∧
    (∀ {α β γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      {U : NeighborhoodSystem γ} (g : ApproximableMap W U) (f : ApproximableMap V W),
      PFmap (g.comp f) = (PFmap g).comp (PFmap f)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α),
      PFmap (idMap V) = idMap V.PowerDomain) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (P : ComputablePresentation V) (Q : ComputablePresentation W)
      (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
      (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b)
      (consW : ℕ → ℕ) (hconsWp : Nat.Primrec consW)
      (hconsWs : ∀ a b, consW (Nat.pair a b) = 1 ↔ ∃ k, Q.X k ⊆ Q.X a ∩ Q.X b)
      {f : ApproximableMap V W} (hf : ComputableMap P Q f),
      ComputableMap (V.PDPresentation P consV hconsVp hconsVs)
        (W.PDPresentation Q consW hconsWp hconsWs) (PFmap f)) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (P : ComputablePresentation V) (Q : ComputablePresentation W)
      {f : ApproximableMap V W} (hf : ComputableMap P Q f),
      REPred₂ (fun c d => (PFmap f).rel (V.Ypd P c) (W.Ypd Q d))) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (P : ComputablePresentation V) (Q : ComputablePresentation W)
      (f : ApproximableMap V W) {c d : ℕ},
      (PFmap f).rel (V.Ypd P c) (W.Ypd Q d) ↔
        ∀ a ∈ decodeList c, ∃ b ∈ decodeList d, f.rel (P.X a) (Q.X b)) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (f : ApproximableMap V W) {L₁ : List (Set α)} {L₂ : List (Set β)}
      (hL₁ : ∀ X ∈ L₁, V.mem X) (hL₂ : ∀ Y ∈ L₂, W.mem Y),
      (PFmap f).rel (⋃ X ∈ L₁, V.upSet X) (⋃ Y ∈ L₂, W.upSet Y) ↔
        ∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y) :=
  ⟨@PFmapComb_toElementMap, ⟨@PFmap_comp, ⟨@PFmap_idMap,
    ⟨@PFmap_isComputable, ⟨@PFmap_isComputable_Ypd, ⟨@PFmap_rel_Ypd_iff, @PFmap_rel_fin⟩⟩⟩⟩⟩⟩

