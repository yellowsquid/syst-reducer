module NormalForm

import Data.SnocList.Elem
import Term
import Thinning

-- Neutrals and Normals --------------------------------------------------------

public export
data Neutral : SnocList Ty -> Ty -> Type
public export
data Normal : SnocList Ty -> Ty -> Type

data Neutral where
  Var : (i : Elem ty ctx) -> Neutral ctx ty
  App : Neutral ctx (ty ~> ty') -> Normal ctx ty -> Neutral ctx ty'
  Rec : Neutral ctx N -> Normal ctx ty -> Normal (ctx :< ty) ty -> Neutral ctx ty

data Normal where
  Ntrl : Neutral ctx ty -> Normal ctx ty
  Abs : Normal (ctx :< ty) ty' -> Normal ctx (ty ~> ty')
  Zero : Normal ctx N
  Succ : Normal ctx N -> Normal ctx N

%name Neutral n, m, k
%name Normal n, m, k

-- Forgetting ------------------------------------------------------------------

export
forgetNtrl : Neutral ctx ty -> Term ctx ty
export
forgetNorm : Normal ctx ty -> Term ctx ty

forgetNtrl (Var i) = Var i
forgetNtrl (App n m) = App (forgetNtrl n) (forgetNorm m)
forgetNtrl (Rec n m k) = Rec (forgetNtrl n) (forgetNorm m) (forgetNorm k)

forgetNorm (Ntrl n) = forgetNtrl n
forgetNorm (Abs n) = Abs (forgetNorm n)
forgetNorm Zero = Zero
forgetNorm (Succ n) = Succ (forgetNorm n)

-- Weakening -------------------------------------------------------------------

export
wknNtrl : Neutral ctx ty -> ctx `Thins` ctx' -> Neutral ctx' ty
export
wknNorm : Normal ctx ty -> ctx `Thins` ctx' -> Normal ctx' ty

wknNtrl (Var i) thin = Var (index thin i)
wknNtrl (App n m) thin = App (wknNtrl n thin) (wknNorm m thin)
wknNtrl (Rec n m k) thin = Rec (wknNtrl n thin) (wknNorm m thin) (wknNorm k $ keep thin)

wknNorm (Ntrl n) thin = Ntrl (wknNtrl n thin)
wknNorm (Abs n) thin = Abs (wknNorm n $ keep thin)
wknNorm Zero thin = Zero
wknNorm (Succ n) thin = Succ (wknNorm n thin)
