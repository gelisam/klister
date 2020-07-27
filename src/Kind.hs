module Kind where


data Kind
  = KStar
  | KFun Kind Kind
  deriving (Show, Eq)

kFun :: [Kind] -> Kind -> Kind
kFun args result = foldr KFun result args
