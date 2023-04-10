-- try it
variable (p q r : Prop)

theorem and_swap : p ∧ q -> q ∧ p := fun h : p ∧ q => ⟨h.right, h.left⟩

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (h: p ∧ q) =>
      show q ∧ p from ⟨ h.right, h.left ⟩)
    (fun (h: q ∧ p) =>
      show p ∧ q from ⟨ h.right, h.left ⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h: p ∨ q) =>
      Or.elim h
        (fun x: p => show q ∨ p from Or.inr x )
        (fun x: q => show q ∨ p from Or.inl x ))
    (fun (h: q ∨ p) =>
      Or.elim h
        (fun x: q => show p ∨ q from Or.inr x )
        (fun x: p => show p ∨ q from Or.inl x ))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      show p ∧ (q ∧ r) from ⟨ h.left.left, ⟨ h.left.right, h.right ⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
      show (p ∧ q) ∧ r from ⟨⟨ h.left, h.right.left ⟩, h.right.right⟩)

def tr {a b : Prop} ( h : a ∨ b ) : b ∨ a :=
  Or.elim h
    (fun x: a => show b ∨ a from Or.inr x )
    (fun x: b => show b ∨ a from Or.inl x )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun g : p ∨ q =>
          Or.elim g
            (fun x: p => show p ∨ (q ∨ r) from Or.inl x )
            (fun x: q => show p ∨ (q ∨ r) from Or.inr (Or.inl x )))
        (fun g : r =>
          show p ∨ (q ∨ r) from Or.inr (Or.inr g)))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun g : p =>
          show (p ∨ q) ∨ r from Or.inl (Or.inl g))
        (fun g : q ∨ r =>
          Or.elim g
            (fun x: q => show (p ∨ q) ∨ r from Or.inl (Or.inr x ))
            (fun x: r => show (p ∨ q) ∨ r from Or.inr x )))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : (p ∧ (q ∨ r)) =>
      Or.elim h.right
        (fun x: q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨h.left, x⟩)
        (fun x: r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨h.left, x⟩
        ))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun x: (p ∧ q) =>
          show p ∧ (q ∨ r) from ⟨x.left, Or.inl x.right⟩)
        (fun x: (p ∧ r) =>
          show p ∧ (q ∨ r) from ⟨x.left, Or.inr x.right⟩
        ))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : (p ∨ (q ∧ r)) =>
      Or.elim h
        (fun x: p =>
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl x, Or.inl x⟩)
        (fun x: (q ∧ r) =>
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr x.left, Or.inr x.right⟩
        ))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim h.left
        (fun x: p =>

          show p ∨ (q ∧ r) from Or.inl x)

        (fun x: q =>
          Or.elim h.right
            (fun k : p =>
              show p ∨ (q ∧ r) from Or.inl k)
            (fun k : r =>
              show p ∨ (q ∧ r) from Or.inr ⟨x, k⟩
            )
        ))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h: (p -> (q -> r)) =>
      fun a: (p ∧ q) =>
        show r from (h a.left) a.right)
    (fun h: p ∧ q -> r =>
      fun f:p =>
        fun s: q =>
          show r from h ⟨f, s⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h: ((p ∨ q) → r) =>
      let x := fun y: p => h (Or.inl y)
      let z := fun y: q => h (Or.inr y)
      show (p → r) ∧ (q → r) from ⟨x, z⟩
    )
    (fun h: (p → r) ∧ (q → r)=>
      fun x: (p ∨ q) =>
        x.elim
          (fun x: p => h.left x)
          (fun x: q => h.right x)
    )

theorem morgan: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h: ¬(p ∨ q) =>
      let l := fun x: p => h (Or.inl x)
      let r := fun x: q => h (Or.inr x)
      show ¬p ∧ ¬q from ⟨l, r⟩)
    (fun h: ¬p ∧ ¬q =>
      fun z: (p ∨ q) =>
        z.elim
          (fun x: p => h.left x)
          (fun x: q => h.right x))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h:¬p ∨ ¬q =>
    fun z: (p ∧ q) =>
      h.elim
        (fun x: ¬p => x z.left)
        (fun x: ¬q => x z.right)

example : ¬(p ∧ ¬p) :=
  fun h: (p ∧ ¬p) =>
    show False from h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun h: (p ∧ ¬q) =>
    show  ¬(p → q) from (fun z: p -> q =>
      show False from h.right (z h.left))

example : ¬p → (p → q) :=
  fun h: ¬p =>
    fun k: p =>
      False.elim (h k)

example : (¬p ∨ q) → (p → q) :=
  fun h: ¬p ∨ q =>
    fun a: p =>
      h.elim
        (fun x: ¬p => False.elim (x a))
        (fun x: q => x)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h: p ∨ False =>
      h.elim
        (fun a: p => a)
        (fun a: False => False.elim a))
    (fun h: p =>
      Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h: p ∧ False =>
      h.right)
    (fun h: False =>
      False.elim h)

example : (p → q) → (¬q → ¬p) :=
  fun h: p -> q =>
    fun b: ¬q =>
      fun c: p =>
        show False from b (h c)







open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h: (p -> q ∨ r) =>
    (em q).elim
      (fun a: q => Or.inl (fun _: p => a))
      (fun a: ¬q => Or.inr (fun x: p =>
        (h x).elim
          (fun b: q => absurd b a)
          (fun b: r => b) ))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h: ¬(p ∧ q) =>
    (em p).elim
      (fun _: p =>
        (em q).elim
          (fun b: q =>
            let x := fun y: p => show False from h (⟨y, b⟩)
            Or.inl x)
          (fun b: ¬q => Or.inr b))
      (fun a: ¬p =>
        Or.inl a)

theorem impl_nqnp  : (¬q → ¬p) → (p → q) :=
  fun h: (¬q → ¬p) =>
    (em q).elim
      (fun k: q =>
        fun _: p => k)
      (fun k: ¬q =>
        fun a: p => absurd a (h k) )

example (hnpq : ¬(p -> q)): p ∧ ¬q :=
  (em p).elim
    (fun hp : p =>
      (em q).elim
        (fun hq: q => absurd (fun (_ : p) => hq) hnpq)
        (fun hnq : ¬q => ⟨hp, hnq⟩ )
    )
    (fun hnp : ¬p =>
        absurd (impl_nqnp p q (fun _: ¬q => hnp)) hnpq)

theorem iff_swap : (a <-> b) -> (b <-> a) :=
  fun (h : a <-> b) =>
    Iff.intro h.mpr h.mp

theorem sw (h :p <-> q) :(¬p <-> ¬q) :=
  Iff.intro
    (fun x: ¬p =>
      (em q).elim
        (fun c: q => absurd (h.mpr c) x)
        (fun c: ¬q => c))
    (fun x: ¬q =>
      (em p).elim
        (fun c: p => absurd (h.mp c) x)
        (fun c: ¬p => c))

example : (p → q) → (¬p ∨ q) :=
  fun h: p -> q =>
    byCases
      (fun x: p => Or.inr (h x))
      (fun x: ¬p => Or.inl x)


example : p ∨ ¬p :=
  (em p).elim
    (fun x:p => Or.inl x)
    (fun x: ¬p => Or.inr x)

theorem impl2 (hpq: p -> q) :¬p ∨ q :=
  (em p).elim
    (fun hp: p => Or.inr (hpq hp))
    (fun hnp : ¬p => Or.inl hnp)

theorem impl : (p -> q) -> ¬p ∨ q :=
  fun (hpq : p->q) =>
    (em p).elim
      (fun hp: p => Or.inr (hpq hp))
      (fun hnp : ¬p => Or.inl hnp)

example : (((p → q) → p) → p) :=
  fun h: ((p → q) → p) =>
    (em p).elim
      (fun hp: p => hp)
      (fun hnp: ¬p => h (impl_nqnp p q (fun _: ¬q => hnp)))
