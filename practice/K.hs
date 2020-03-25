{-# language DefaultSignatures,ScopedTypeVariables,TypeSynonymInstances #-}
module K where
import System.Process;  import Data.Int; import Text.Printf; import Data.List
import Test.QuickCheck; import Test.QuickCheck.Monadic
type Str=String; type I64=Int64; type I32=Int32
fmt::PrintfType r=>String->r; fmt=printf

exeval :: Str->IO Str
exeval s = do{writeFile"/tmp/in"$unlines[s]; system"k</tmp/in>/tmp/out"; readFile"/tmp/out"}

sure :: KH t=>Str->(t->Bool)->Property
sure s a = monadicIO $ kh<$>run(exeval s) >>= assert.a

addi (a::I64)(b::I64) = sure (fmt"%d+%d"a b) (==a+b)
addi0 (a::I64)        = sure (fmt"%d+0"a) (==a)
sumi (as::[I64])      = as/=[] ==> sure ("+/"<>hk as) (==sum as)
divi (a::I64)(b::I64) = a/=0   ==> sure (fmt"%d/%d"a b) (==b`div`a)

hk_round a = sure(hk a)(==a)

class HK a where hk::a->Str; default hk::Show a=>a->Str; hk=show
instance HK I32; instance HK I64
instance HK a => HK [a] where hk[]="()"; hk a="("<>(concat.intersperse";".fmap hk$a)<>")"

class KH a where kh::Str->a; default kh::Read a=>Str->a; kh=read
instance KH I32; instance KH I64
