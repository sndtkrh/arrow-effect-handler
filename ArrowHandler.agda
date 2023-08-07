{-# OPTIONS --safe #-}
module ArrowHandler where

{-
open import Relation.Binary.PropositionalEquality
    using (_≡_)
    renaming (refl to ≡refl)
open import Data.Product
    using ()
    renaming (_×_ to _∧_; _,_ to _and_)
open import Relation.Nullary
    using (¬_)
open import Data.Unit.Base
    using (⊤; tt)
open import Data.Empty
    using (⊥)
-}

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma public
  renaming (Σ to Sigma; fst to proj₁; snd to proj₂; _,_ to _and_)
  hiding (module Σ)
open import Agda.Primitive

_∧_ : {a b : Level} → (A : Set a) (B : Set b) → Set (a ⊔ b)
A ∧ B = Sigma A (λ x → B)

data ⊤ : Set where
    tt : ⊤

data ⊥ : Set where

infix 3 ¬_
¬_ : {a : Level} → Set a → Set a
¬ P = P → ⊥

-- base types
data BaseType : Set where
    Unit : BaseType
    Nat : BaseType
    Bool : BaseType

-- types
data Ty : Set where
    Base : BaseType → Ty -- β ∈ Btype : base type
    Prod : Ty → Ty → Ty  -- A₁ × A₂    : product type
    Fn   : Ty → Ty → Ty  -- A ⟶ B     : function type
    Arr  : Ty → Ty → Ty  -- A ⇝ B      : arrow type

-- primitive types
Φ : Ty → Set
Φ (Base β) = ⊤
Φ (Prod s t) = Φ s ∧ Φ t
Φ (Fn s t) = Φ s ∧ Φ t
Φ (Arr s t) = ⊥

Fn-syntax : Ty → Ty → Ty
Fn-syntax = Fn
syntax Fn-syntax A B = A ⟶ B

-- contexts
infixl 5 _,_
data Ctx : Set where
    ⋄ : Ctx
    _,_ : Ctx → Ty → Ctx

-- concatnation of two context
infixl 5 _ʻ_
_ʻ_ : Ctx → Ctx → Ctx
Γ ʻ ⋄ = Γ
Γ ʻ (Δ , A) = (Γ ʻ Δ) , A

infix 4 _∈_
data _∈_ : Ty → Ctx → Set where
    hd : ∀ {A Γ}   → A ∈ Γ , A
    tl : ∀ {A B Γ} → A ∈ Γ → A ∈ Γ , B

-- signature
record Signature : Set₁ where
    field
        O : Set
        arity : O → BaseType
        coarity : O → BaseType

-- definition of the type system for arrow calculus with operations and handlers
data Term : Signature → Ctx → Ty → Set
data Command : Signature → Ctx → Ctx → Ty → Set
data Handler : Signature → Ty → Ty → Set

data Term where
    var : ∀ {Σ Γ A}
        → A ∈ Γ     -- x : A ∈ Γ
                     -------------
        → Term Σ Γ A -- Γ ⊢ x : A

    unit : ∀ {Σ Γ}
        → Term Σ Γ (Base Unit) -- Γ ⊢ () : Unit
    
    true : ∀ {Σ Γ}
        → Term Σ Γ (Base Bool) -- Γ ⊢ true : Bool

    false : ∀ {Σ Γ}
        → Term Σ Γ (Base Bool) -- Γ ⊢ false : Bool

    if[_]then[_]else[_] : ∀ {Σ Γ A}
        → Term Σ Γ (Base Bool) -- Γ ⊢ m : Bool
        → Term Σ Γ A           -- Γ ⊢ n₁ : A
        → Term Σ Γ A           -- Γ ⊢ n₂ : A
                               -------------------------------
        → Term Σ Γ A           -- Γ ⊢ if m then n₁ else n₂ : A
    
    ⟨_,_⟩ : ∀ {Σ Γ A₁ A₂}
        → Term Σ Γ A₁           -- Γ ⊢ M₁ : A₁
        → Term Σ Γ A₂           -- Γ ⊢ M₂ : A₂
                                ---------------------------
        → Term Σ Γ (Prod A₁ A₂) -- Γ ⊢ ⟨ M₁ , M₂ ⟩ : A₁ × A₂

    lam : ∀ {Σ Γ A B}
        → Term Σ (Γ , A) B   -- Γ , x : A ⊢ M : B
                             -------------------------------
        → Term Σ Γ (Fn A B)  -- Γ         ⊢ λ x . M : A ⟶ B

    app : ∀ {Σ Γ A B}
        → Term Σ Γ (Fn A B) -- Γ ⊢ M : A ⟶ B
        → Term Σ Γ A        -- Γ ⊢ N : A
                            -----------------
        → Term Σ Γ B        -- Γ ⊢ M N : B

    clam : ∀ {Σ Γ A B}
        → Command Σ Γ (⋄ , A) B -- Γ ; x : A ⊢ P ! B
                                -------------------------------
        → Term Σ Γ (Arr A B)    -- Γ         ⊢ λᵒ x . P : A ⇝ B

data Command where
    arr : ∀ {Σ Γ Δ A}
        → Term Σ (Γ ʻ Δ) A -- Γ , Δ ⊢ M : A
                           ------------------
        → Command Σ Γ Δ A  -- Γ ; Δ ⊢ [M] ! A

    letin : ∀ {Σ Γ Δ A B}
        → Command Σ Γ Δ A       -- Γ ;         Δ ⊢ P ! A
        → Command Σ Γ (Δ , A) B -- Γ ; x : A , Δ ⊢ Q ! B
                                -------------------------------------
        → Command Σ Γ Δ B       -- Γ ;         Δ ⊢ let x ← P in Q ! B
    
    capp : ∀ {Σ Γ Δ A B}
        → Term Σ Γ (Arr A B) -- Γ     ⊢ L : A ⇝ B
        → Term Σ (Γ ʻ Δ) A   -- Γ , Δ ⊢ M : A
                             --------------------
        → Command Σ Γ Δ B    -- Γ ; Δ ⊢ L ● M ! B
    
    op : ∀ {Σ Γ Δ}
        → (o : Signature.O Σ)                           -- o : γ ⇾ δ
        → Term Σ (Γ ʻ Δ) (Base (Signature.coarity Σ o)) -- Γ , Δ ⊢ M : γ
                                                        -------------------
        → Command Σ Γ Δ (Base (Signature.arity Σ o))    -- Γ ; Δ ⊢ o(M) : δ

    handle : ∀ {Σ Γ Δ C D}
        → Command Σ Γ Δ C -- Γ ; Δ ⊢ P ! C
        → Handler Σ C D   --       ⊢ H : C ⇒ D
                          ------------------------------
        → Command Σ Γ Δ D -- Γ ; Δ ⊢ handle P with H ! D

data Handler where
    handler : ∀ {Σ C D}
        → Φ C → Φ D
        → Command Σ ⋄ (⋄ , C) D -- ⋄         ; x : C ⊢ P ! D
        → ((op : Signature.O Σ) -- k : δ ⇝ D ; z : γ ⊢ Qop ! D, for each (op : γ ⇾ δ) ∈ Σ
            → Command Σ (⋄ , Arr (Base (Signature.arity Σ op)) D) (⋄ , (Base (Signature.coarity Σ op))) D)
                                -----------------------------------------------------------
        → Handler Σ C D         -- ⊢ H : C ⇒ D

-- definition of value
data Value {Σ Γ} : ∀ {A} → Term Σ Γ A → Set where
    V-var : ∀ {A} {x : A ∈ Γ}
        → Value (var x)
    V-unit  : Value {Σ} {Γ} unit
    V-true  : Value {Σ} {Γ} true
    V-false : Value {Σ} {Γ} false
    V-pair : ∀ {A₁ A₂}
        → {v₁ : Term Σ Γ A₁}
        → {v₂ : Term Σ Γ A₂}
        → Value {Σ} {Γ} {A₁} v₁
        → Value {Σ} {Γ} {A₂} v₂
        → Value ⟨ v₁ , v₂ ⟩
    V-lam : ∀ {A B} {t : Term Σ (Γ , A) B}
        → Value (lam t)
    V-clam : ∀ {A B} {t : Command Σ Γ (⋄ , A) B}
        → Value (clam t)

data Valueᶜ : ∀ {Σ Γ Δ A} → Command Σ Γ Δ A → Set where
    V-arr : ∀ {Σ Γ Δ A} {v : Term Σ (Γ ʻ Δ) A}
        → Value v
        → Valueᶜ {Σ} {Γ} {Δ} (arr v)

-- if `CallOp p o v` then the command `p` is calling the operation `o` with an argument `v`
data CallOp {Σ Γ Δ} : {A : Ty} → Command Σ Γ Δ A → (o : Signature.O Σ) → Term Σ (Γ ʻ Δ) (Base (Signature.coarity Σ o)) → Set where
    trivially : {o : Signature.O Σ} {v : Term Σ (Γ ʻ Δ) (Base (Signature.coarity Σ o))}
        → Value {Σ} {Γ ʻ Δ} {Base (Signature.coarity Σ o)} v
        → CallOp {_} {_} {_} {Base (Signature.arity Σ o)} (op o v) o v
    let[op]in : ∀ {A B}
        {o : Signature.O Σ} {v : Term Σ (Γ ʻ Δ) (Base (Signature.coarity Σ o))}
        {p : Command Σ Γ Δ A} {q : Command Σ Γ (Δ , A) B}
        → CallOp p o v
        → CallOp (letin p q) o v

ext : ∀ {Γ Γ'}
    → (∀ {A} → A ∈ Γ → A ∈ Γ')
    → ∀ {A B}
    → A ∈ (Γ , B)
    → A ∈ (Γ' , B)
ext ρ hd = hd
ext ρ (tl a) = tl (ρ a)

extʻ₁ : ∀ {Γ Δ A} → A ∈ Γ → A ∈ (Γ ʻ Δ)
extʻ₁ {Γ} {⋄} a = a
extʻ₁ {Γ} {Δ , x} a = tl (extʻ₁ a)

extʻ₂ : ∀ {Γ Δ A} → A ∈ Δ → A ∈ (Γ ʻ Δ)
extʻ₂ {Γ} {.(_ , _)} hd = hd
extʻ₂ {Γ} {.(_ , _)} (tl a) = tl (extʻ₂ a)

assoc-ctx : ∀ {Γ Γ' Γ'' A} → (A ∈ Γ ʻ Γ' ʻ Γ'') → (A ∈ Γ ʻ (Γ' ʻ Γ''))
assoc-ctx {Γ} {Γ'} {⋄} a = a
assoc-ctx {Γ} {Γ'} {Γ'' , B} {A} a = ext (assoc-ctx {Γ} {Γ'}) a

concat-rename : ∀ {A} {Γ Γ' Δ Δ'} →
    (A ∈ Γ → A ∈ Γ') →
    (A ∈ Δ → A ∈ Δ') →
    A ∈ (Γ ʻ Δ) → A ∈ (Γ' ʻ Δ')
concat-rename {_} {Γ} {Γ'} {⋄} {⋄} ρ₁ ρ₂ a = ρ₁ a
concat-rename {_} {Γ} {Γ'} {Δ , A} {⋄} ρ₁ ρ₂ hd with ρ₂ hd
concat-rename {A} {Γ} {Γ'} {Δ , A} {⋄} ρ₁ ρ₂ hd | ()
concat-rename {_} {Γ} {Γ'} {Δ , A} {⋄} ρ₁ ρ₂ (tl a) = ρ₁ (concat-rename (λ z → z) (λ z → ρ₂ (tl z)) a)
concat-rename {A} {Γ} {Γ'} {⋄} {Δ' , A'} ρ₁ ρ₂ a = extʻ₁ (ρ₁ a)
concat-rename {A} {Γ} {Γ'} {Δ , A} {Δ' , A'} ρ₁ ρ₂ hd with ρ₂ hd
concat-rename {A} {Γ} {Γ'} {Δ , A} {Δ' , .A} ρ₁ ρ₂ hd | hd = hd
concat-rename {A} {Γ} {Γ'} {Δ , A} {Δ' , A'} ρ₁ ρ₂ hd | tl a = extʻ₂ (ρ₂ hd)
concat-rename {A} {Γ} {Γ'} {Δ , B} {Δ' , A'} ρ₁ ρ₂ (tl a) = concat-rename ρ₁ (λ z → ρ₂ (tl z)) a

renameᵗ : ∀ {Γ Γ' Σ}
    → (∀ {A} → A ∈ Γ → A ∈ Γ')
    → ∀ {A}
    → Term Σ Γ A
    → Term Σ Γ' A
renameᶜ : ∀ {Γ Γ' Δ Δ' Σ}
    → (∀ {A} → A ∈ Γ → A ∈ Γ')
    → (∀ {A} → A ∈ Δ → A ∈ Δ')
    → ∀ {A}
    → Command Σ Γ Δ A
    → Command Σ Γ' Δ' A

renameᵗ ρ (var x) = var (ρ x)
renameᵗ ρ unit = unit
renameᵗ ρ true = true
renameᵗ ρ false = false
renameᵗ ρ if[ m ]then[ n₁ ]else[ n₂ ] = if[ renameᵗ ρ m ]then[ renameᵗ ρ n₁ ]else[ renameᵗ ρ n₂ ]
renameᵗ ρ ⟨ m₁ , m₂ ⟩ = ⟨ renameᵗ ρ m₁ , renameᵗ ρ m₂ ⟩
renameᵗ ρ (lam m) = lam (renameᵗ (ext ρ) m)
renameᵗ ρ (app l m) = app (renameᵗ ρ l) (renameᵗ ρ m)
renameᵗ ρ (clam p) = clam (renameᶜ ρ (λ A → A) p)

renameᶜ ρ τ (arr m) = arr (renameᵗ (concat-rename ρ τ) m)
renameᶜ ρ τ (letin p q) = letin (renameᶜ ρ τ p) (renameᶜ ρ (ext τ) q)
renameᶜ {Γ} {Γ'} {Δ} {Δ'} ρ τ (capp t s) = capp (renameᵗ ρ t) (renameᵗ (concat-rename ρ τ) s)
renameᶜ {Γ} {Γ'} {Δ} {Δ'} ρ τ (op o t) = op o (renameᵗ (concat-rename ρ τ) t)
renameᶜ {Γ} {Γ'} {Δ} {Δ'} ρ τ (handle r h) = handle (renameᶜ ρ τ r) h

-- make-continuation is used to define reduction for `handle F[op(v)] with h`
{-
let xₙ ← ⋯ (let x₂ ← (let x₁ ← op(v) in p₁) in p₂) ⋯ in pₙ
↦
λᵒ y . handle [let xₙ ← ⋯ (let x₂ ← (let x₁ ← arr(y) in p₁) in p₂) ⋯ in pₙ] with h
-}
make-continuation : ∀ {C D Σ} {r : Command Σ ⋄ ⋄ C} {o : Signature.O Σ} {v}
    → CallOp r o v
    → Handler Σ C D
    → Term Σ ⋄ (Arr (Base (Signature.arity Σ o)) D)
make-continuation r-call-o h = clam (handle (aux r-call-o) h)
    where
    aux : ∀ {C Σ} {r : Command Σ ⋄ ⋄ C} {o : Signature.O Σ} {v : Term Σ ⋄ (Base (Signature.coarity Σ o))}
        → CallOp {Σ} {⋄} {⋄} {C} r o v
        → Command Σ ⋄ (⋄ , Base (Signature.arity Σ o)) C
    aux (trivially _) = arr (var hd)
    aux {C} {Σ} (let[op]in {A} {_} {o} {v} {r} {r'} r-calls-o) =
        letin (aux r-calls-o) (renameᶜ (λ ()) (λ { hd → hd }) r')

extsᵗ : ∀ {Σ Γ Γ'}
    → (∀ {A} → A ∈ Γ → Term Σ Γ' A) -- substitution
    → ∀ {A B}
    → A ∈ (Γ , B)
    → Term Σ (Γ' , B) A
extsᵗ σ hd = var hd
extsᵗ σ (tl a) = renameᵗ tl (σ a)

concat-subst : ∀ {A} {Σ Γ Γ' Δ Δ'}
    → (A ∈ Γ → Term Σ Γ' A)
    → (A ∈ Δ → Term Σ (Γ' ʻ Δ') A)
    → A ∈ (Γ ʻ Δ) → Term Σ (Γ' ʻ Δ') A
concat-subst {A} {Σ} {Γ} {Γ'} {⋄} {Δ'} σ τ a = renameᵗ extʻ₁ (σ a)
concat-subst {.A} {Σ} {Γ} {Γ'} {Δ , A} σ τ hd = τ hd
concat-subst {A} {Σ} {Γ} {Γ'} {Δ , B} σ τ (tl a) = concat-subst σ (λ z → τ (tl z)) a


-- substitution for terms and commands
substᵗ : ∀ {Σ Γ Γ'}
    → (∀ {A} → A ∈ Γ → Term Σ Γ' A)
    → ∀ {A}
    → Term Σ Γ A
    → Term Σ Γ' A
substᶜ : ∀ {Σ Γ Γ' Δ Δ'}
    → (∀ {A} → A ∈ Γ → Term Σ Γ' A)
    → (∀ {A} → A ∈ Δ → Term Σ (Γ' ʻ Δ') A)
    → ∀ {A}
    → Command Σ Γ Δ A
    → Command Σ Γ' Δ' A

substᵗ σ (var x) = σ x
substᵗ σ unit = unit
substᵗ σ true = true
substᵗ σ false = false
substᵗ σ if[ m ]then[ n₁ ]else[ n₂ ] = if[ substᵗ σ m ]then[ substᵗ σ n₁ ]else[ substᵗ σ n₂ ]
substᵗ σ ⟨ m₁ , m₂ ⟩ = ⟨ substᵗ σ m₁ , substᵗ σ m₂ ⟩
substᵗ σ (lam m) = lam (substᵗ (extsᵗ σ) m)
substᵗ σ (app m n) = app (substᵗ σ m) (substᵗ σ n)
substᵗ {Σ} {Γ} {Γ'} σ (clam p) = clam (substᶜ σ Δsubst-var p)
    where
    Δsubst-var : ∀ {B} → {A : Ty} → A ∈ ⋄ , B → Term Σ (Γ' ʻ (⋄ , B)) A
    Δsubst-var {A} hd = var hd

substᶜ σ τ (arr m) = arr (substᵗ (concat-subst σ τ) m)
substᶜ {Σ} {Γ} {Γ'} {Δ} {Δ'} σ τ (letin p₁ p₂) = letin (substᶜ σ τ p₁) (substᶜ σ τ' p₂)
    where
    τ' : ∀ {A B} → B ∈ Δ , A → Term Σ (Γ' ʻ (Δ' , A)) B
    τ' hd = var hd
    τ' {A} {B} (tl ρ) = renameᵗ (λ a → assoc-ctx {Γ'} {Δ'} {⋄ , A} (extʻ₁ {Γ' ʻ Δ'} {⋄ , A} a))  (τ ρ)
substᶜ σ τ (capp t s) = capp (substᵗ σ t) (substᵗ (concat-subst σ τ) s)
substᶜ σ τ (op o t) = op o (substᵗ (concat-subst σ τ) t)
substᶜ {Σ} {Γ} {Γ'} {Δ} {Δ'} σ τ {A} (handle r h) = handle (substᶜ σ τ r) h

-- special cases of substitution
substᵗ0 : ∀ {Σ Γ A B}
    → Term Σ (Γ , B) A
    → Term Σ Γ B
    → Term Σ Γ A
substᵗ0 {Σ} {Γ} {A} {B} t s = substᵗ {Σ} {Γ , B} {Γ} σ {A} t
    where
    σ : ∀ {A} → A ∈ (Γ , B) → Term Σ Γ A
    σ hd = s
    σ (tl a) = var a

substᶜ0 : ∀ {Σ Γ Δ A B}
    → Command Σ Γ (Δ , B) A
    → Term Σ (Γ ʻ Δ) B
    → Command Σ Γ Δ A
substᶜ0 {Σ} {Γ} {Δ} {_} {B} p t = substᶜ var τ p
    where
    τ : ∀ {A} → A ∈ Δ , B → Term Σ (Γ ʻ Δ) A
    τ hd = t
    τ (tl a) = var (extʻ₂ a)

substᶜ00 : ∀ {Σ Γ Δ A X Y}
    → Command Σ (Γ , X) (Δ , Y) A
    → Term Σ Γ X
    → Term Σ (Γ ʻ Δ) Y
    → Command Σ Γ Δ A
substᶜ00 {Σ} {Γ} {Δ} {A} {X} {Y} p s t = substᶜ σ τ p
    where
    σ : ∀ {B} → B ∈ Γ , X → Term Σ Γ B
    σ {B} hd = s
    σ {B} (tl a) = var a
    
    τ : ∀ {B} → B ∈ Δ , Y → Term Σ (Γ ʻ Δ) B
    τ {B} hd = t
    τ {B} (tl a) = renameᵗ extʻ₂ (var a)


-- operational semantics
data _⟶ᵗ_ {Σ Γ} : ∀ {A} → (Term Σ Γ A) → (Term Σ Γ A) → Set where
    βᵗ : ∀ {A B} {m : Term Σ (Γ , A) B} {w : Term Σ Γ A}
        → Value w
        → (app (lam m) w) ⟶ᵗ substᵗ0 m w
    βᵗif[true] : ∀ {A} {t₁ t₂ : Term Σ Γ A}
        → if[ true ]then[ t₁ ]else[ t₂ ] ⟶ᵗ t₁
    βᵗif[false] : ∀ {A} {t₁ t₂ : Term Σ Γ A}
        → if[ false ]then[ t₁ ]else[ t₂ ] ⟶ᵗ t₂
    ξᵗif : ∀ {A} {m m' : Term Σ Γ (Base Bool)} {n₁ n₂ : Term Σ Γ A}
        → m ⟶ᵗ m'
        → if[ m ]then[ n₁ ]else[ n₂ ] ⟶ᵗ if[ m' ]then[ n₁ ]else[ n₂ ]
    ξᵗpair₁ : ∀ {A₁ A₂} {m₁ m₁' : Term Σ Γ A₁} {m₂ : Term Σ Γ A₂}
        → m₁ ⟶ᵗ m₁'
        → ⟨ m₁ , m₂ ⟩ ⟶ᵗ ⟨ m₁' , m₂ ⟩
    ξᵗpair₂ : ∀ {A₁ A₂} {v₁ : Term Σ Γ A₁} {m₂ m₂' : Term Σ Γ A₂}
        → Value v₁
        → m₂ ⟶ᵗ m₂'
        → ⟨ v₁ , m₂ ⟩ ⟶ᵗ ⟨ v₁ , m₂' ⟩
    ξᵗapp₁ : ∀ {A B} {m m' : Term Σ Γ (A ⟶ B)} {n : Term Σ Γ A}
        → m ⟶ᵗ m'
        → app m n ⟶ᵗ app m' n
    ξᵗapp₂ : ∀ {A B} {v : Term Σ Γ (A ⟶ B)} {n n' : Term Σ Γ A}
        → Value v
        → n ⟶ᵗ n'
        → app v n ⟶ᵗ app v n'

data _⟶ᶜ_ {Σ} : ∀ {A} → (Command Σ ⋄ ⋄ A) → (Command Σ ⋄ ⋄ A) → Set where
    βᶜletin : ∀ {A B} {w : Term Σ ⋄ A} {p : Command Σ ⋄ (⋄ , A) B}
        → Value w
        → letin (arr w) p ⟶ᶜ substᶜ0 p w
    βᶜclam : ∀ {A B} {p : Command Σ ⋄ (⋄ , A) B} {w : Term Σ ⋄ A}
        → Value w
        → capp (clam p) w ⟶ᶜ substᶜ0 p w
    βᶜhandle-op : ∀ {C ΦC D ΦD}
        {o : Signature.O Σ} {r : Command Σ ⋄ ⋄ C}
        {v : Term Σ ⋄ (Base (Signature.coarity Σ o))}
        {p : Command Σ ⋄ (⋄ , C) D}
        {qs : (op : Signature.O Σ) → Command Σ (⋄ , Arr (Base (Signature.arity Σ op)) D) (⋄ , (Base (Signature.coarity Σ op))) D}
        → (r-calls-o[v] : CallOp r o v)
        -- handle F[o(v)] with { p ; qs } ⟶ (qs o)[ λᵒ y . handle F[ arr(y) ] with { p ; qs } / k , v / x ]
        → (handle r (handler ΦC ΦD p qs)) ⟶ᶜ substᶜ00 (qs o) (make-continuation r-calls-o[v] (handler ΦC ΦD p qs)) v
    βᶜhandle-val : ∀ {C ΦC D ΦD}
        {v : Term Σ ⋄ C}
        {p : Command Σ ⋄ (⋄ , C) D}
        {qs : (op : Signature.O Σ) → Command Σ (⋄ , Arr (Base (Signature.arity Σ op)) D) (⋄ , (Base (Signature.coarity Σ op))) D}
        → Value v
        → (handle (arr v) (handler ΦC ΦD p qs)) ⟶ᶜ substᶜ0 p v
    ξᶜarr : ∀ {A} {m : Term Σ ⋄ A} {m' : Term Σ ⋄ A}
        → m ⟶ᵗ m'
        → _⟶ᶜ_ {Σ} {A} (arr m) (arr m')
    ξᶜcapp₁ : ∀ {A B} {m m' : Term Σ ⋄ (Arr A B)} {n : Term Σ ⋄ A}
        → m ⟶ᵗ m'
        → capp m n ⟶ᶜ capp m' n
    ξᶜcapp₂ : ∀ {A B} {w : Term Σ ⋄ (Arr A B)} {n n' : Term Σ ⋄ A}
        → Value w
        → n ⟶ᵗ n'
        → capp w n ⟶ᶜ capp w n'
    ξᶜop : ∀ {o : Signature.O Σ} {m m' : Term Σ ⋄ (Base (Signature.coarity Σ o))}
        → m ⟶ᵗ m'
        → _⟶ᶜ_ {Σ} {Base (Signature.arity Σ o)} (op o m) (op o m')
    ξᶜletin : ∀ {A B} {p p' : Command Σ ⋄ ⋄ A} {q : Command Σ ⋄ (⋄ , A) B}
        → p ⟶ᶜ p'
        → letin p q ⟶ᶜ letin p' q
    ξᶜhandle : ∀ {C D} {p p' : Command Σ ⋄ ⋄ C} {h : Handler Σ C D}
        → p ⟶ᶜ p'
        → handle p h ⟶ᶜ handle p' h

data _≅ʰ_ {Σ C D} : Handler Σ C D → Handler Σ C D → Set where
    eq-handler : {p : Command Σ ⋄ (⋄ , C) D}
        {qs qs' : (op : Signature.O Σ) → Command Σ (⋄ , Arr (Base (Signature.arity Σ op)) D) (⋄ , (Base (Signature.coarity Σ op))) D}
        → {ΦC : Φ C} → {ΦD : Φ D}
        → (∀ op → qs op ≡ qs' op)
        → (handler ΦC ΦD p qs) ≅ʰ (handler ΦC ΦD p qs')

data _≅ᶜ_ {Σ Γ Δ} : ∀ {D} → (Command Σ Γ Δ D) → (Command Σ Γ Δ D) → Set where
    eq-handle : ∀ {C D} {p : Command Σ Γ Δ C} {h h' : Handler Σ C D}
        → h ≅ʰ h'
        → handle p h ≅ᶜ handle p h'

-- reflexive and transitive closure of ⟶ᵗ
infix  2 _⟶ᵗ*_
infix  1 beginᵗ_
infixr 2 _⟶ᵗ⟨_⟩_
infix  3 _∎ᵗ
data _⟶ᵗ*_ {Σ A} : (Term Σ ⋄ A) → (Term Σ ⋄ A) → Set where

    _∎ᵗ : (m : Term Σ ⋄ A)
        → m ⟶ᵗ* m

    _⟶ᵗ⟨_⟩_ : (m₁ : Term Σ ⋄ A) {m₂ m₃ : Term Σ ⋄ A}
        → m₁ ⟶ᵗ m₂
        → m₂ ⟶ᵗ* m₃
        → m₁ ⟶ᵗ* m₃

beginᵗ_ : ∀ {Σ A} {m n : Term Σ ⋄ A}
    → m ⟶ᵗ* n
    → m ⟶ᵗ* n
beginᵗ m⟶ᵗ*n = m⟶ᵗ*n

-- reflexive and transitive closure of ⟶ᶜ
infix  2 _⟶ᶜ*_
infix  1 beginᶜ_
infixr 2 _⟶ᶜ⟨_⟩_
infixr 2 _≅ᶜ⟨_⟩_
infix  3 _∎ᶜ
data _⟶ᶜ*_ {Σ A} : (Command Σ ⋄ ⋄ A) → (Command Σ ⋄ ⋄ A) → Set where

    _∎ᶜ : (p : Command Σ ⋄ ⋄ A)
        → p ⟶ᶜ* p

    _≡ᶜ⟨_⟩_ : (p : Command Σ ⋄ ⋄ A) {q q' : Command Σ ⋄ ⋄ A}
        → p ≡ q
        → q ⟶ᶜ* q'
        → p ⟶ᶜ* q'
    
    _≅ᶜ⟨_⟩_ : (p : Command Σ ⋄ ⋄ A) {q q' : Command Σ ⋄ ⋄ A}
        → p ≅ᶜ q
        → q ⟶ᶜ* q'
        → p ⟶ᶜ* q'

    _⟶ᶜ⟨_⟩_ : (p₁ : Command Σ ⋄ ⋄ A) {p₂ p₃ : Command Σ ⋄ ⋄ A}
        → p₁ ⟶ᶜ  p₂
        → p₂ ⟶ᶜ* p₃
        → p₁ ⟶ᶜ* p₃

beginᶜ_ : ∀ {Σ A} {p q : Command Σ ⋄ ⋄ A}
    → p ⟶ᶜ* q
    → p ⟶ᶜ* q
beginᶜ p⟶ᶜ*q = p⟶ᶜ*q

-- Proposition: values are normal form
value-do-not-reduce : ∀ {Σ A} {v : Term Σ ⋄ A}
    → Value v
    → ∀ m
    → ¬ (v ⟶ᵗ m)
value-do-not-reduce {Σ} {Base β} {.(var _)} V-var _ ()
value-do-not-reduce {Σ} {Base .Unit} {.unit} V-unit _ ()
value-do-not-reduce {Σ} {Base .Bool} {.true} V-true _ ()
value-do-not-reduce {Σ} {Base .Bool} {.false} V-false _ ()
value-do-not-reduce {Σ} {Prod A₁ A₂} {.(⟨ _ , _ ⟩)} (V-pair v₁-val v₂-val) (⟨ m₁ , m₂ ⟩) (ξᵗpair₁ v₁⟶ᵗm₁) = value-do-not-reduce v₁-val m₁ v₁⟶ᵗm₁
value-do-not-reduce {Σ} {Prod A₁ A₂} {.(⟨ _ , _ ⟩)} (V-pair v₁-val v₂-val) (⟨ v₁ , m₂ ⟩) (ξᵗpair₂ v₁-is-value v₂⟶ᵗm₂) = value-do-not-reduce v₂-val m₂ v₂⟶ᵗm₂
value-do-not-reduce {Σ} {Fn A B} {.(var _)} V-var _ ()
value-do-not-reduce {Σ} {Fn A B} {.(lam _)} V-lam _ ()
value-do-not-reduce {Σ} {Arr A B} {.(var _)} V-var _ ()
value-do-not-reduce {Σ} {Arr A B} {.(clam _)} V-clam _ ()

arrvalue-do-not-reduce : ∀ {Σ A} {v : Term Σ ⋄ A}
    → Value v
    → ∀ p
    → ¬ (arr v ⟶ᶜ p)
arrvalue-do-not-reduce v-value (arr t) (ξᶜarr v⟶t) =
    value-do-not-reduce v-value t v⟶t


-- the statement of progress
data Progressᵗ {Σ A} (t : Term Σ ⋄ A) : Set where
    stepᵗ : ∀ {s : Term Σ ⋄ A} → t ⟶ᵗ s → Progressᵗ t
    doneᵗ : Value t → Progressᵗ t

data Progressᶜ {Σ A} (p : Command Σ ⋄ ⋄ A) : Set where
    stepᶜ : ∀ {p' : Command Σ ⋄ ⋄ A} → p ⟶ᶜ p' → Progressᶜ p
    call : ∀ {o v} → CallOp p o v → Progressᶜ p
    doneᶜ : Valueᶜ p → Progressᶜ p

-- Proposition: progress
progressᵗ : ∀ {Σ A} → (t : Term Σ ⋄ A) → Progressᵗ t
progressᵗ (lam t) = doneᵗ V-lam
progressᵗ unit = doneᵗ V-unit
progressᵗ true = doneᵗ V-true
progressᵗ false = doneᵗ V-false
progressᵗ if[ true ]then[ n₁ ]else[ n₂ ] = stepᵗ βᵗif[true]
progressᵗ if[ false ]then[ n₁ ]else[ n₂ ] = stepᵗ βᵗif[false]
progressᵗ if[ if[ m ]then[ n₁ ]else[ n₂ ] ]then[ l₁ ]else[ l₂ ] with progressᵗ if[ m ]then[ n₁ ]else[ n₂ ]
progressᵗ if[ if[ m ]then[ n₁ ]else[ n₂ ] ]then[ l₁ ]else[ l₂ ] | stepᵗ x = stepᵗ (ξᵗif x)
progressᵗ if[ app m l ]then[ _ ]else[ _ ] with progressᵗ (app m l)
progressᵗ if[ app m l ]then[ _ ]else[ _ ] | stepᵗ x = stepᵗ (ξᵗif x)
progressᵗ ⟨ m₁ , m₂ ⟩ with progressᵗ m₁
progressᵗ ⟨ m₁ , m₂ ⟩ | stepᵗ m₁⟶ᵗm₁' = stepᵗ (ξᵗpair₁ m₁⟶ᵗm₁')
progressᵗ ⟨ m₁ , m₂ ⟩ | doneᵗ m₁-is-value with progressᵗ m₂
progressᵗ ⟨ m₁ , m₂ ⟩ | doneᵗ m₁-is-value | stepᵗ m₂⟶ᵗm₂' = stepᵗ (ξᵗpair₂ m₁-is-value m₂⟶ᵗm₂')
progressᵗ ⟨ m₁ , m₂ ⟩ | doneᵗ m₁-is-value | doneᵗ m₂-is-value = doneᵗ (V-pair m₁-is-value m₂-is-value)
progressᵗ (app m n) with progressᵗ m
progressᵗ (app m n) | stepᵗ m⟶m' = stepᵗ (ξᵗapp₁ m⟶m')
progressᵗ (app .(lam _) n) | doneᵗ V-lam with progressᵗ n
progressᵗ (app .(lam _) n) | doneᵗ V-lam | stepᵗ n⟶n' = stepᵗ (ξᵗapp₂ V-lam n⟶n')
progressᵗ (app .(lam _) n) | doneᵗ V-lam | doneᵗ x = stepᵗ (βᵗ x)
progressᵗ (clam p) = doneᵗ V-clam

progressᶜ : ∀ {Σ A} → (p : Command Σ ⋄ ⋄ A) → Progressᶜ p
progressᶜ (arr m) with progressᵗ m
progressᶜ (arr m) | stepᵗ m⟶ᵗm' = stepᶜ (ξᶜarr m⟶ᵗm')
progressᶜ (arr m) | doneᵗ m-is-value = doneᶜ (V-arr m-is-value)
progressᶜ (letin p₁ p₂) with progressᶜ p₁
progressᶜ (letin p₁ p₂) | stepᶜ p⟶ᶜp' = stepᶜ (ξᶜletin p⟶ᶜp')
progressᶜ (letin p₁ p₂) | call (calling) = call (let[op]in calling)
progressᶜ (letin (arr v) p₂) | doneᶜ (V-arr v-is-value) = stepᶜ (βᶜletin v-is-value)
progressᶜ (capp l m) with progressᵗ l
progressᶜ (capp l m) | stepᵗ l⟶ᵗl' = stepᶜ (ξᶜcapp₁ l⟶ᵗl')
progressᶜ (capp l m) | doneᵗ l-is-value with progressᵗ m
progressᶜ (capp l m) | doneᵗ l-is-value | stepᵗ m⟶ᵗm' = stepᶜ (ξᶜcapp₂ l-is-value m⟶ᵗm')
progressᶜ (capp (clam p) s) | doneᵗ V-clam | doneᵗ m-is-value = stepᶜ (βᶜclam m-is-value)
progressᶜ (op o m) with progressᵗ m
progressᶜ (op o m) | stepᵗ m⟶ᵗm' = stepᶜ (ξᶜop m⟶ᵗm')
progressᶜ (op o m) | doneᵗ m-is-value = call (trivially m-is-value)
progressᶜ (handle r h) with progressᶜ r
progressᶜ (handle r h) | stepᶜ r⟶ᶜr' = stepᶜ (ξᶜhandle r⟶ᶜr')
progressᶜ (handle r (handler ΦC ΦD p qs)) | call r-calls-o[v] = stepᶜ (βᶜhandle-op r-calls-o[v])
progressᶜ (handle (arr v) (handler ΦC ΦD p qs)) | doneᶜ (V-arr v-value) = stepᶜ (βᶜhandle-val v-value)


module Example where
    
    data Ops : Set where
        get : Ops
    
    Σ : Signature
    Σ = record { O = Ops ; arity = λ {get → Bool}; coarity = λ {get → Unit} }
    
    h[true] : Handler Σ (Base Bool) (Base Bool)
    h[true] = (handler tt tt (arr (var hd)) (λ {get → capp (var hd) true}))
    h[false] : Handler Σ (Base Bool) (Base Bool)
    h[false] = (handler tt tt (arr (var hd)) (λ {get → capp (var hd) false}))
    
    _ : handle (op get unit) h[true] ⟶ᶜ* arr true
    _ = beginᶜ
            (handle (op get unit) h[true])
        ⟶ᶜ⟨ βᶜhandle-op (trivially V-unit) ⟩
            capp (clam (handle (arr (var hd)) h[true])) true
        ⟶ᶜ⟨ βᶜclam V-true ⟩
            substᶜ0 (handle (arr (var hd)) h[true]) true
        ≅ᶜ⟨ eq-handle (eq-handler (λ {get → ≡refl})) ⟩
            handle (arr true) h[true]
        ⟶ᶜ⟨ βᶜhandle-val V-true ⟩
            arr true
        ∎ᶜ

    _ : handle (op get unit) h[false] ⟶ᶜ* arr false
    _ = beginᶜ
            (handle (op get unit) h[false])
        ⟶ᶜ⟨ βᶜhandle-op (trivially V-unit) ⟩
            capp (clam (handle (arr (var hd)) h[false])) false
        ⟶ᶜ⟨ βᶜclam V-false ⟩
            substᶜ0 (handle (arr (var hd)) h[false]) false
        ≅ᶜ⟨ eq-handle (eq-handler (λ {get → ≡refl})) ⟩
            handle (arr false) h[false]
        ⟶ᶜ⟨ βᶜhandle-val V-false ⟩
            arr false
        ∎ᶜ
 