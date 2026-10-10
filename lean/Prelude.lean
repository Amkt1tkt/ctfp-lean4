/-!
# CTFP-Lean4 公共前导（Prelude）

全书统一使用的范畴论基础定义。各章若需要，就把**需要的那几段**原样复制进
章节开头的 ```` ```lean hidden ```` 代码块（读者看不到，但校验脚本会编译它）。
这样每章的 Lean 代码都是自包含的，可以直接粘贴到 https://live.lean-lang.org 运行。

约定：
* 复合写作 `g ⊚ f`，读作 “g 在 f 之后”，与原书 `g ∘ f` 方向一致（从右往左）。
* 态射类型写作 `a ⟶ b`（`\hom` 或 `\-->`），恒等态射写作 `𝟙 a`。
* 不依赖 Mathlib，只用 Lean 核心库。
-/

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace CTFP

/-! ## §1 范畴 -/

/-- 范畴：对象 + 态射 + 复合 + 恒等，满足单位律与结合律。 -/
class Category (Obj : Type u) where
  /-- 从 `a` 到 `b` 的态射所组成的类型（hom-set）。 -/
  Hom : Obj → Obj → Type v
  /-- 每个对象上的恒等态射。 -/
  id : (a : Obj) → Hom a a
  /-- 复合：`comp g f` 表示先 `f` 后 `g`。 -/
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f := by intros; rfl
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f := by intros; rfl
  assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp h (comp g f) = comp (comp h g) f := by intros; rfl

infixr:10 " ⟶ " => Category.Hom
infixr:80 " ⊚ " => Category.comp
notation "𝟙" => Category.id

open Category

/-- 类型与函数构成的范畴 **Type**（原书中的 **Set**/**Hask**）。三条定律都是 `rfl`。 -/
instance typeCategory : Category (Type u) where
  Hom a b := a → b
  id _ := fun x => x
  comp g f := fun x => g (f x)

/-! ## §2 函子（范畴之间的映射） -/

/-- 范畴之间的函子：把对象映到对象、态射映到态射，并保持恒等与复合。
（与 Lean 自带的、只作用在 `Type → Type` 上的 `Functor` 类区分开。） -/
structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

/-! ## §3 自然变换 -/

/-- 自然变换 `α : F ⟹ G`：每个对象一个分量，满足自然性方块交换。 -/
structure NatTrans {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  app : (a : C) → (F.obj a ⟶ G.obj a)
  naturality : ∀ {a b : C} (f : a ⟶ b), G.map f ⊚ app a = app b ⊚ F.map f

infixr:50 " ⟹ " => NatTrans

/-! ## §4 常用小工具 -/

/-- 对偶范畴 `Cᵒᵖ`：对象相同、箭头反转。 -/
def Op (C : Type u) : Type u := C

instance opCategory (C : Type u) [Category.{u, v} C] : Category.{u, v} (Op C) where
  Hom a b := @Category.Hom C _ b a
  id a := @Category.id C _ a
  comp g f := @Category.comp C _ _ _ _ f g
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

end CTFP

/-! ## 自检 -/
section Check
open CTFP

/-- 注意：裸 lambda 需要标注成 `Nat ⟶ Nat`，Lean 才知道用哪个范畴实例。 -/
def inc : Nat ⟶ Nat := fun n => n + 1
def dbl : Nat ⟶ Nat := fun n => n * 2
/-- 提示：先给态射起名并写出 `Nat ⟶ Nat` 签名，再用 `⊚`，Lean 才能确定用哪个范畴实例。 -/
example : inc ⊚ dbl = fun n => n * 2 + 1 := rfl

/-- 恒等函子 -/
def idFunctor (C : Type u) [Category.{u, v} C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `List` 作为 Type 上的自函子 -/
def listFunctor : CFunctor (Type u) (Type u) where
  obj := List
  map f := List.map f
  map_id a := by funext (xs : List a); simp [Category.id]
  map_comp {a _ _} f g := by funext (xs : List a); simp [Category.comp]

/-- `List.reverse` 是自然变换 List ⟹ List -/
def reverseNat : listFunctor.{u} ⟹ listFunctor.{u} where
  app _ := List.reverse
  naturality {a _} f := by funext (xs : List a); exact List.map_reverse

end Check
