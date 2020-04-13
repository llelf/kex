{-# language DefaultSignatures,NoMonomorphismRestriction,ScopedTypeVariables,TypeSynonymInstances #-}
module K where
import System.Process;  import Data.Int; import Text.Printf; import Data.List
import Test.QuickCheck; import Test.QuickCheck.Monadic
type Str=String; type I64=Int64; type J=I64; type I32=Int32; type I=I32

fmt=printf
(nani,nanj)=(minBound,minBound)::(I,J)

exeval :: Str->IO Str
exeval s = do{writeFile"/tmp/in"$unlines[s]; system"k</tmp/in>/tmp/out"; readFile"/tmp/out"}

sure :: KH t=>Str->(t->Bool)->Property
sure s a = monadicIO $ kh<$>run(exeval s) >>= assert.a

addii (a::J)(b::J) = sure (fmt"%d+%d"a b) (==a+b)
addiC (a::J)(b::J) = sure (fmt"%d+%d"b a) (==a+b)
addi0 (a::J)       = sure (fmt"%d+0"a) (==a)
add0i (a::J)       = sure (fmt"0+%d"a) (==a)

addiA1 (a::J)(b::J)(c::J) = sure (fmt"%d+%d+%d"a b c) (==a+b+c)
addiA2 (a::J)(b::J)(c::J) = sure (fmt"%d+(%d+%d)"a b c) (==a+b+c)

sumi (as::[J])    = as/=[] ==> sure ("+/"<>hk as) (==sum as)
divi (a::J)(b::J) = a/=0   ==> sure (fmt"%d/%d"a b) (==b`div`a)


hk_round a = sure(hk a)(==a)

class HK a where hk::a->Str; default hk::Show a=>a->Str; hk=show
instance HK I; instance HK J
instance HK a => HK [a] where hk[]="()"; hk a="("<>(concat.intersperse";".fmap hk$a)<>")"

class KH a where kh::Str->a; default kh::Read a=>Str->a; kh=read
instance KH I; instance KH J

qc = quickCheckWith(stdArgs{maxSuccess=2000,maxSize=1000})

