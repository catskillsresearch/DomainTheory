module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}







variable (P₀ P₁)













section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **`f ⊗ g` is computable.** Writing each smash code via its *effective* product index
(`smashEnum_eq_eff`), the relation `(smashEnum n) (f⊗g) (smashEnum' m)` decodes to: `m` improper
(the codomain master absorbs everything), or `m` proper together with `f`'s and `g`'s r.e. relations
on the effective coordinate indices. R.e.-ness then follows from `hf`, `hg`, the codomain properness
deciders, and closure of r.e. predicates under `∨`/`∧`/primitive-recursive substitution. -/
theorem smashMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMapS P₀.toScott P₀'.toScott f)
    (hg : IsComputableMapS P₁.toScott P₁'.toScott g) :
    IsComputableMapS (smashPresentation P₀ P₁) (smashPresentation P₀' P₁') (smashMap f g) := by
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.2 P₁.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
  -- `f`'s r.e. relation on `(effL n, m.1)`; `g`'s on `(effR n, m.2)`
  have Hf : REPred (fun t => f.rel (P₀.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx)) (P₀'.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.comp ((heffLp.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.comp ((heffRp.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧
      P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    ((proper₀_dec P₀').comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Hf.and Hg)))
  show (smashMap f g).rel (smashEnum P₀ P₁ t.unpair.1) (smashEnum P₀' P₁' t.unpair.2) ↔ _
  have heq : smashEnum P₀ P₁ t.unpair.1 = prodNbhd
      (P₀.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx))
      (P₁.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) := smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁ t.unpair.1
  by_cases hJPm : P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, A', B', hWAB, hW'AB, -, -, hfr, hgr⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hW'AB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective (heq.symm.trans hWAB)
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hW'AB
        exact Or.inr ⟨hJPm, hfr, hgr⟩
    · rintro (hnp | ⟨-, hfr, hgr⟩)
      · exact absurd hJPm hnp
      · exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
          smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
          Or.inr ⟨_, _, _, _, heq, smashEnum_proper hJPm, hJPm.1, hJPm.2, hfr, hgr⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
        smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
        Or.inl (smashEnum_master hJPm)⟩

end SmashFunctor
end Smash
end DomainTheory.NeighbourhoodSystems
