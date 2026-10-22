module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ProjPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ofIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.IsUniversal

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}


/-- **`D ⊴ E` composed with an isomorphism `D ≅ᴰ D'` on the left is still `D ⊴ E`** — immediate
from unfolding `⊴` and composing the two `DomainIso`s (`OrderIso.trans`). -/
theorem trianglelefteq_of_isomorphic_left {D : NeighborhoodSystem α} {D' : NeighborhoodSystem β}
    {E : NeighborhoodSystem γ} (hDD' : D ≅ᴰ D') (hD'E : D' ⊴ E) : D ⊴ E := by
  obtain ⟨F, hFE, ⟨eD'F⟩⟩ := hD'E
  obtain ⟨eDD'⟩ := hDD'
  exact ⟨F, hFE, ⟨eDD'.trans eD'F⟩⟩

/-- **`⊴` is transitive.** `D ⊴ E` and `E ⊴ F` give `D ⊴ F`: unfold both to a subsystem `D' ◁ E`
(`D ≅ᴰ D'`) and `E' ◁ F` (`E ≅ᴰ E'`); `ProjPair.ofSubsystem` turns `D' ◁ E`/`E' ◁ F` into projection
pairs, `ProjPair.ofIso` turns `E ≅ᴰ E'` into one too, and composing all three (`ProjPair.comp`) gives
a projection pair `D' ⇄ F`, hence `D' ⊴ F` (Lemma 6.15). Gluing back `D ≅ᴰ D'` on the left
(`trianglelefteq_of_isomorphic_left`) finishes. -/
theorem trianglelefteq_trans {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (h1 : D ⊴ E) (h2 : E ⊴ F) : D ⊴ F := by
  obtain ⟨D', hD'E, ⟨eDD'⟩⟩ := h1
  obtain ⟨E', hE'F, ⟨eEE'⟩⟩ := h2
  have pD'F : ProjPair D' F :=
    ((ProjPair.ofSubsystem hD'E).comp (ProjPair.ofIso eEE')).comp (ProjPair.ofSubsystem hE'F)
  have hD'F : D' ⊴ F :=
    trianglelefteq_of_projectionPair pD'F.inj pD'F.proj pD'F.proj_comp_inj pD'F.inj_comp_proj_le
  exact trianglelefteq_of_isomorphic_left ⟨eDD'⟩ hD'F

end DomainTheory.NeighbourhoodSystems
