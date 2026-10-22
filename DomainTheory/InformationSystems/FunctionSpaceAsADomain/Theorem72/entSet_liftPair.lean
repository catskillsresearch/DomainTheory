module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.ProdCon_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndFinset_liftPair

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Product entailment between lifted pairs from component entailments. -/
theorem entSet_liftPair {u u' : Finset α} {v v' : Finset β}
    (hu' : u' ∈ A.Con) (hv' : v' ∈ B.Con)
    (hEntu : A.EntSet u' u) (hEntv : B.EntSet v' v) :
    (productSystem A B).EntSet (liftPair A B u' v') (liftPair A B u v) := by
  intro p hp
  have hCon : ProdCon A B (liftPair A B u' v') := ProdCon_liftPair A B hu' hv'
  unfold liftPair at hp
  rcases mem_funion.mp hp with hp | hp
  · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      have hsub : u' ⊆ fstFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [fstFinset_liftPair]
        exact subset_funion_left _ _ hz
      exact A.ent_trans hCon.1 hu'
        (fun z hz => A.ent_refl hCon.1 (hsub hz)) (hEntu x hx)
    · intro _
      exact B.ent_bot hCon.2
  · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      exact A.ent_bot hCon.1
    · intro _
      have hsub : v' ⊆ sndFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hz
      exact B.ent_trans hCon.2 hv'
        (fun z hz => B.ent_refl hCon.2 (hsub hz)) (hEntv y hy)

end InfoSys

end DomainTheory.InformationSystems
