module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
import DomainTheory.InformationSystems.InformationSystems.EntSet

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def liftPair (u : Finset α) (v : Finset β) : Finset (ProdToken A B) :=
  liftLeft A B u ∪' liftRight A B v

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem liftLeft_funion (u u' : Finset α) :
    liftLeft A B (u ∪' u') = liftLeft A B u ∪' liftLeft A B u' := by
  ext p
  constructor
  · intro hp
    rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
    rcases funion.mem.mp hx with hx | hx
    · exact funion.mem.mpr (Or.inl ((liftLeft.mem A B).2 ⟨x, hx, rfl⟩))
    · exact funion.mem.mpr (Or.inr ((liftLeft.mem A B).2 ⟨x, hx, rfl⟩))
  · intro hp
    rcases funion.mem.mp hp with hp | hp
    · rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
      exact (liftLeft.mem A B).2 ⟨x, funion.mem.mpr (Or.inl hx), rfl⟩
    · rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
      exact (liftLeft.mem A B).2 ⟨x, funion.mem.mpr (Or.inr hx), rfl⟩

end InfoSys
end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem liftRight_funion (v v' : Finset β) :
    liftRight A B (v ∪' v') = liftRight A B v ∪' liftRight A B v' := by
  ext p
  constructor
  · intro hp
    rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
    rcases funion.mem.mp hy with hy | hy
    · exact funion.mem.mpr (Or.inl ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
    · exact funion.mem.mpr (Or.inr ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases funion.mem.mp hp with hp | hp
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inl hy), rfl⟩
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inr hy), rfl⟩

end InfoSys
end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem ProdCon_liftPair {u : Finset α} {v : Finset β}
    (hu : u ∈ A.Con) (hv : v ∈ B.Con) : ProdCon A B (liftPair A B u v) := by
  constructor
  · unfold liftPair
    rw [fstFinset.funion, liftLeft.fstFinset_eq]
    have hEnt : A.EntSet u (fstFinset A B (liftRight A B v)) := fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp (liftRight.fstFinset_eq A B v hx)
      subst this
      exact A.ent_bot hu
    exact EntSet.union_mem A hu hEnt
  · unfold liftPair
    rw [sndFinset.funion, liftRight.sndFinset_eq]
    have hEnt : B.EntSet v (sndFinset A B (liftLeft A B u)) := fun y hy => by
      have : y = B.bot := Finset.mem_singleton.mp (liftLeft.sndFinset_eq A B u hy)
      subst this
      exact B.ent_bot hv
    have h := EntSet.union_mem B hv hEnt
    rwa [funion.comm] at h

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem fstFinset_liftPair (u : Finset α) (v : Finset β) :
    fstFinset A B (liftPair A B u v) =
      u ∪' fstFinset A B (liftRight A B v) := by
  unfold liftPair
  rw [fstFinset.funion, liftLeft.fstFinset_eq]

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem sndFinset_liftPair (u : Finset α) (v : Finset β) :
    sndFinset A B (liftPair A B u v) =
      sndFinset A B (liftLeft A B u) ∪' v := by
  unfold liftPair
  rw [sndFinset.funion, liftRight.sndFinset_eq]

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem entSet_liftPair {u u' : Finset α} {v v' : Finset β}
    (hu' : u' ∈ A.Con) (hv' : v' ∈ B.Con)
    (hEntu : A.EntSet u' u) (hEntv : B.EntSet v' v) :
    (productSystem A B).EntSet (liftPair A B u' v') (liftPair A B u v) := by
  intro p hp
  have hCon : ProdCon A B (liftPair A B u' v') := ProdCon_liftPair A B hu' hv'
  unfold liftPair at hp
  rcases funion.mem.mp hp with hp | hp
  · rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      have hsub : u' ⊆ fstFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [fstFinset_liftPair]
        exact funion.subset_left _ _ hz
      exact A.ent_trans hCon.1 hu'
        (fun z hz => A.ent_refl hCon.1 (hsub hz)) (hEntu x hx)
    · intro _
      exact B.ent_bot hCon.2
  · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      exact A.ent_bot hCon.1
    · intro _
      have hsub : v' ⊆ sndFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [sndFinset_liftPair]
        exact funion.subset_right _ _ hz
      exact B.ent_trans hCon.2 hv'
        (fun z hz => B.ent_refl hCon.2 (hsub hz)) (hEntv y hy)

end InfoSys

end DomainTheory.InformationSystems
