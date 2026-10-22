module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.map
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.gFun
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.RootedConst
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.gIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.naryOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.narySum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.naryProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.naryOplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.naryOtimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.inter_ne_of_ne_left
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_mem_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_mem_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}


/-- `gFun T Γ = tok(T({Γ}))`. -/
theorem gFun_eq_master : (T : GExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    gFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .prod a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .oplus a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .otimes a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]

/-- **`λΓ. tok(T({Γ}))` is monotone.** -/
theorem gFun_mono (T : GExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : gFun T Γ ⊆ gFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | oplus a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | otimes a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-- **`λΓ. tok(T({Γ}))` is continuous on `{Γ ∣ Λ ∈ Γ}`.** -/
theorem gFun_continuous (T : GExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ gFun T U ↔ ∃ Γ ∈ ℱ, w ∈ gFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | oplus a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | otimes a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w


theorem gFun_nil_mem : ∀ (T : GExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ gFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _
  | .oplus _ _, _, _, _ => Set.mem_insert _ _
  | .otimes _ _, _, _, _ => Set.mem_insert _ _


theorem nil_mem_gIter (T : GExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ gIter T n
  | 0 => rfl
  | n + 1 => gFun_nil_mem T hT (nil_mem_gIter T hT n)

theorem gIter_mono_step (T : GExpr) (hT : T.RootedConst) :
    ∀ n, gIter T n ⊆ gIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact gFun_nil_mem T hT rfl
  | n + 1 => gFun_mono T (gIter_mono_step T hT n)

theorem gIter_mono (T : GExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    gIter T m ⊆ gIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact gIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem gFun_iter_fixed (T : GExpr) (hT : T.RootedConst) :
    gFun T (⋃ n, gIter T n) = ⋃ n, gIter T n := by
  have hstep := gIter_mono_step T hT
  have hne : (Set.range (gIter T)).Nonempty := ⟨gIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (gIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨gIter T (max i j), ⟨max i j, rfl⟩,
      gIter_mono T hT (le_max_left i j), gIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, gIter T n) ↔ ∃ S ∈ Set.range (gIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨gIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [gFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨gIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **Exercise 6.21/6.20 (token level).** For any `GExpr` `T` whose constants contain `Λ`, there is a
set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem gExists_tok_fixedPoint (T : GExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ gFun T Γ = Γ :=
  ⟨⋃ n, gIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_gIter T hT 0⟩, gFun_iter_fixed T hT⟩

/-- **Exercise 6.21/6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies** for any construct
`T` built from constants, identity, `+`, `×`, `⊕`, `⊗`. -/
theorem gExists_singleton_subsystem (T : GExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := gExists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (gFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · exact hmaster.symm
  · intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]


end Exercise619
end DomainTheory.NeighbourhoodSystems
