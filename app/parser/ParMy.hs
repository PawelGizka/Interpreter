{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParMy where
import AbsMy
import LexMy
import ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn24 :: (Ident) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (Ident)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: (Integer) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> (Integer)
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (String) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (String)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (Program) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (Program)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: ([Def]) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> ([Def])
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Def) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Def)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: ([Stm]) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> ([Stm])
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (Mod) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (Mod)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: (Stm) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> (Stm)
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (Type) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (Type)
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: ([Type]) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> ([Type])
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: ([Arg]) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> ([Arg])
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: (Arg) -> (HappyAbsSyn )
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> (Arg)
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: (Exp) -> (HappyAbsSyn )
happyIn37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn ) -> (Exp)
happyOut37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: (Exp) -> (HappyAbsSyn )
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (Exp)
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (Exp) -> (HappyAbsSyn )
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (Exp)
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: (Exp) -> (HappyAbsSyn )
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> (Exp)
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (Exp) -> (HappyAbsSyn )
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (Exp)
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (Exp) -> (HappyAbsSyn )
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (Exp)
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (Exp) -> (HappyAbsSyn )
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (Exp)
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (Exp) -> (HappyAbsSyn )
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (Exp)
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: (Exp) -> (HappyAbsSyn )
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> (Exp)
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: (Exp) -> (HappyAbsSyn )
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> (Exp)
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: ([Exp]) -> (HappyAbsSyn )
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> ([Exp])
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x00\x00\xc5\x00\x00\x00\xc5\x00\x3a\x00\x3c\x03\x3c\x03\xc5\x00\xc5\x00\x5b\x01\x8c\x00\x7c\x00\x7c\x00\x7c\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x33\x01\x00\x00\x7e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x91\x00\x70\x00\x00\x00\xaa\x00\x5e\x00\x5a\x01\xf8\xff\x2f\x01\x7c\x00\x4b\x00\x8c\x00\x00\x00\x3c\x03\x00\x00\x00\x00\x00\x00\x60\x00\x04\x00\x02\x00\x3d\x00\x2f\x01\x06\x00\xfd\xff\x2f\x01\x2f\x01\x2f\x01\x5b\x00\x2c\x01\x1b\x01\x00\x00\x00\x00\x1b\x01\x44\x01\x88\x00\x19\x01\x00\x00\x47\x01\x00\x00\x00\x00\x00\x00\xfc\xff\x7d\x00\x36\x01\x07\x01\x15\x01\x41\x00\x0d\x01\x5b\x00\x75\x00\x5b\x00\x00\x00\x13\x01\x01\x00\x13\x01\xe5\xff\x13\x01\xc5\x00\x00\x00\x00\x00\x19\x00\x6c\x00\x12\x00\x00\x00\xeb\xff\x04\x01\x00\x00\x5b\x00\x23\x01\x00\x00\x5b\x00\x22\x01\x20\x01\x00\x00\x5b\x00\x5b\x00\x00\x00\x2a\x01\x3c\x03\xc5\x00\x12\x01\x11\x00\x7c\x00\x7c\x00\x7c\x00\x7c\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\x5b\x00\xd3\x00\x00\x00\x1a\x01\x70\x00\x5b\x00\x5b\x00\x3b\x00\x00\x00\x10\x01\x5b\x00\x5e\x00\xaa\x00\xaa\x00\x00\x00\x00\x00\x00\x00\x00\x00\x91\x00\x91\x00\x00\x00\x00\x00\x00\x00\x3c\x03\x00\x00\x00\x00\x3c\x03\xfe\xff\xfa\xff\x00\x00\x00\x00\x18\x01\x5b\x00\x17\x01\xdb\x00\x3a\x00\x00\x00\x3a\x00\x00\x00\x00\x00\x94\x00\xe7\x00\x5b\x00\xea\x00\x00\x00\x00\x00\xf7\x00\x03\x01\xef\x00\xed\xff\x3c\x03\x00\x00\xd4\x00\x00\x00\xf2\x00\x5b\x00\x2a\x00\xe8\x00\x3a\x00\x00\x00\xe3\x00\x3a\x00\x5b\x00\xf9\xff\x3c\x03\x3a\x00\x00\x00\x42\x00\x00\x00\xf1\xff\x00\x00\x00\x00\x3a\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\xd5\x00\xfc\x00\xa3\x00\xeb\x00\xe9\x00\xb5\x01\xca\x00\xaf\x00\xcb\x00\x66\x00\xc4\x00\x86\x03\x83\x03\x6c\x03\x44\x03\x2c\x03\xf3\x02\xc3\x02\xa5\x02\x85\x02\xe5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3f\x03\x9e\x01\x58\x03\x00\x00\xb8\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\x02\xb3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb1\x00\x00\x00\x00\x00\x00\x00\x64\x02\x5a\x02\x43\x02\xa5\x00\x00\x00\x87\x01\x00\x00\x9c\x00\x00\x00\x9c\x00\x00\x00\x00\x00\x87\x01\x00\x00\x00\x00\x00\x00\x00\x00\xa2\x00\x00\x00\x9c\x02\x00\x00\x00\x00\xcd\x00\x00\x00\x00\x00\x00\x00\x39\x02\x22\x02\x00\x00\x00\x00\x92\x00\xc9\x00\x00\x00\x00\x00\x80\x03\x7d\x03\x68\x03\x62\x03\x26\x03\x13\x03\x0d\x03\xfa\x02\xdf\x02\xd8\x02\xbb\x02\x00\x00\x00\x00\x00\x00\x00\x00\xb5\x00\x18\x02\x00\x00\x00\x00\x00\x00\x01\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8d\x00\x00\x00\x00\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\x01\x00\x00\x00\x00\x70\x01\x00\x00\x59\x01\x00\x00\x00\x00\x00\x00\x61\x00\xe0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4d\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd6\x01\x00\x00\x00\x00\x42\x01\x00\x00\x00\x00\x2b\x01\xbf\x01\x00\x00\x13\x00\x14\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfd\x00\x00\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xe6\xff\xe6\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\xcb\xff\xc8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa2\xff\x00\x00\xea\xff\xc3\xff\xc2\xff\xc1\xff\xb9\xff\xb7\xff\xb4\xff\xb1\xff\xaf\xff\xaa\xff\xa7\xff\xa5\xff\xa3\xff\xa1\xff\x00\x00\x00\x00\xc8\xff\x00\x00\xbf\xff\x00\x00\xc0\xff\xe9\xff\xe8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe1\xff\xe0\xff\x00\x00\xc7\xff\xca\xff\x00\x00\xd1\xff\x00\x00\xd0\xff\xce\xff\xcf\xff\x00\x00\xc3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe7\xff\xe5\xff\xe2\xff\x00\x00\x00\x00\x00\x00\xd8\xff\x00\x00\x00\x00\xdd\xff\x00\x00\x00\x00\xdc\xff\xa2\xff\x00\x00\x00\x00\xbb\xff\x00\x00\x00\x00\xcc\xff\x00\x00\xcb\xff\xc8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb8\xff\x00\x00\xb0\xff\xa2\xff\x00\x00\x00\x00\xa0\xff\x00\x00\x00\x00\xa6\xff\xa9\xff\xa8\xff\xac\xff\xae\xff\xab\xff\xad\xff\xb2\xff\xb3\xff\xb5\xff\xb6\xff\xc4\xff\x00\x00\xc6\xff\xc9\xff\xcb\xff\x00\x00\x00\x00\xda\xff\xdb\xff\x00\x00\x00\x00\xa4\xff\x00\x00\x00\x00\xd9\xff\x00\x00\xd4\xff\xd7\xff\x00\x00\x00\x00\x00\x00\xe4\xff\xbd\xff\xdf\xff\xba\xff\x00\x00\xc5\xff\x00\x00\x00\x00\xba\xff\x00\x00\xbc\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xbe\xff\x00\x00\xde\xff\x00\x00\xd5\xff\xd2\xff\x00\x00\xcd\xff\xd6\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x09\x00\x01\x00\x06\x00\x02\x00\x04\x00\x19\x00\x03\x00\x0f\x00\x0f\x00\x0d\x00\x0a\x00\x1b\x00\x07\x00\x29\x00\x2a\x00\x0a\x00\x26\x00\x09\x00\x0a\x00\x18\x00\x13\x00\x05\x00\x19\x00\x33\x00\x2e\x00\x01\x00\x2e\x00\x09\x00\x04\x00\x1d\x00\x2e\x00\x1f\x00\x0f\x00\x21\x00\x0a\x00\x23\x00\x24\x00\x2e\x00\x2e\x00\x2e\x00\x28\x00\x29\x00\x2a\x00\x2e\x00\x2c\x00\x2d\x00\x33\x00\x33\x00\x30\x00\x31\x00\x32\x00\x33\x00\x33\x00\x1d\x00\x33\x00\x1f\x00\x33\x00\x21\x00\x01\x00\x23\x00\x24\x00\x04\x00\x2e\x00\x2e\x00\x28\x00\x29\x00\x2a\x00\x0a\x00\x2c\x00\x2d\x00\x05\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x01\x00\x10\x00\x11\x00\x04\x00\x0f\x00\x27\x00\x15\x00\x16\x00\x19\x00\x0a\x00\x09\x00\x1d\x00\x2e\x00\x1f\x00\x18\x00\x21\x00\x01\x00\x23\x00\x24\x00\x04\x00\x02\x00\x00\x00\x28\x00\x29\x00\x2a\x00\x0a\x00\x2c\x00\x2d\x00\x1d\x00\x2e\x00\x30\x00\x31\x00\x32\x00\x07\x00\x23\x00\x2e\x00\x33\x00\x13\x00\x0c\x00\x28\x00\x29\x00\x2a\x00\x01\x00\x07\x00\x1d\x00\x04\x00\x0a\x00\x30\x00\x31\x00\x32\x00\x23\x00\x0a\x00\x04\x00\x04\x00\x04\x00\x28\x00\x0f\x00\x08\x00\x0a\x00\x1b\x00\x0b\x00\x0c\x00\x0c\x00\x30\x00\x31\x00\x32\x00\x2e\x00\x12\x00\x04\x00\x09\x00\x1d\x00\x33\x00\x17\x00\x17\x00\x09\x00\x06\x00\x23\x00\x1d\x00\x2e\x00\x09\x00\x0a\x00\x28\x00\x0d\x00\x23\x00\x18\x00\x05\x00\x00\x00\x07\x00\x28\x00\x30\x00\x31\x00\x32\x00\x05\x00\x1d\x00\x07\x00\x06\x00\x30\x00\x31\x00\x32\x00\x23\x00\x1c\x00\x00\x00\x1e\x00\x00\x00\x28\x00\x00\x00\x01\x00\x02\x00\x09\x00\x0a\x00\x10\x00\x11\x00\x30\x00\x31\x00\x32\x00\x15\x00\x16\x00\x09\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x00\x00\x01\x00\x02\x00\x07\x00\x0d\x00\x07\x00\x09\x00\x0b\x00\x0c\x00\x0b\x00\x0c\x00\x03\x00\x04\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x00\x00\x01\x00\x02\x00\x14\x00\x0e\x00\x17\x00\x18\x00\x18\x00\x12\x00\x29\x00\x2a\x00\x07\x00\x06\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x00\x00\x01\x00\x02\x00\x04\x00\x1e\x00\x05\x00\x1b\x00\x07\x00\x08\x00\x14\x00\x18\x00\x05\x00\x12\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\x30\x00\x2e\x00\x05\x00\x03\x00\x07\x00\x08\x00\x05\x00\x0e\x00\x05\x00\x0e\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\x04\x00\x0f\x00\x05\x00\x0f\x00\x07\x00\x08\x00\x30\x00\x12\x00\x29\x00\x30\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\x0f\x00\x33\x00\x05\x00\x33\x00\x07\x00\x08\x00\x04\x00\x33\x00\x09\x00\x33\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\x30\x00\x03\x00\x05\x00\x04\x00\x07\x00\x08\x00\x33\x00\x30\x00\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\xff\xff\x07\x00\x08\x00\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\xff\xff\x07\x00\x08\x00\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x07\x00\xff\xff\xff\xff\xff\xff\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\xff\xff\x07\x00\x08\x00\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x1a\x00\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\x20\x00\xff\xff\x22\x00\xff\xff\xff\xff\x25\x00\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x2b\x00\x00\x00\x01\x00\x02\x00\xff\xff\x00\x00\x01\x00\x02\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\xff\xff\xff\xff\x0d\x00\x0e\x00\x0f\x00\x10\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\xff\xff\x0d\x00\x0e\x00\x0f\x00\x0d\x00\x0e\x00\x0f\x00\x0d\x00\x0e\x00\x0f\x00\x0d\x00\x0e\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x7e\x00\x26\x00\x6f\x00\x77\x00\x27\x00\xae\x00\x79\x00\xbd\x00\xa6\x00\x70\x00\x28\x00\xc1\x00\x71\x00\x3b\x00\x3c\x00\x72\x00\x9c\x00\x3e\x00\xa7\x00\x69\x00\x78\x00\x8f\x00\xa7\x00\xff\xff\x60\x00\x26\x00\x60\x00\xbb\x00\x27\x00\x29\x00\x60\x00\x4c\x00\x9d\x00\x4d\x00\x28\x00\x2a\x00\x4e\x00\x60\x00\x60\x00\x60\x00\x2b\x00\x3b\x00\x3c\x00\x60\x00\x4f\x00\x50\x00\xff\xff\xff\xff\x17\x00\x2c\x00\x2d\x00\xff\xff\xff\xff\x29\x00\xff\xff\x4c\x00\xff\xff\x4d\x00\x26\x00\x2a\x00\x4e\x00\x27\x00\x60\x00\x60\x00\x2b\x00\x3b\x00\x3c\x00\x28\x00\x4f\x00\x50\x00\xc2\x00\x9f\x00\x17\x00\x2c\x00\x2d\x00\x26\x00\x73\x00\x74\x00\x27\x00\x5f\x00\xb7\x00\x75\x00\x76\x00\xac\x00\x28\x00\xac\x00\x29\x00\x60\x00\x4c\x00\x69\x00\x4d\x00\x26\x00\x2a\x00\x4e\x00\x27\x00\x77\x00\xb1\x00\x2b\x00\x3b\x00\x3c\x00\x28\x00\x4f\x00\x50\x00\x29\x00\x60\x00\x17\x00\x2c\x00\x2d\x00\x38\x00\x2a\x00\x60\x00\xff\xff\x78\x00\x39\x00\x2b\x00\x3b\x00\x3c\x00\x26\x00\x71\x00\x29\x00\x27\x00\x72\x00\x17\x00\x2c\x00\x2d\x00\x2a\x00\x28\x00\x27\x00\x63\x00\x63\x00\x2b\x00\x5c\x00\x64\x00\x28\x00\x9e\x00\x65\x00\x66\x00\x66\x00\x17\x00\x2c\x00\x2d\x00\x60\x00\x67\x00\x27\x00\x6b\x00\x29\x00\xff\xff\x68\x00\x7f\x00\xa8\x00\x6f\x00\x2a\x00\x29\x00\x60\x00\x3e\x00\x91\x00\x2b\x00\x70\x00\x2a\x00\x69\x00\x56\x00\x9a\x00\x48\x00\x2b\x00\x17\x00\x2c\x00\x2d\x00\x52\x00\x29\x00\x48\x00\x58\x00\x17\x00\x2c\x00\x2d\x00\x2a\x00\xb3\x00\x60\x00\xb4\x00\x6c\x00\x2b\x00\x17\x00\x18\x00\x19\x00\x3e\x00\x3f\x00\x73\x00\x74\x00\x17\x00\x2c\x00\x2d\x00\x75\x00\x76\x00\x79\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x80\x00\x17\x00\x18\x00\x19\x00\x38\x00\x36\x00\x38\x00\x45\x00\x90\x00\x3d\x00\x3c\x00\x3d\x00\x54\x00\x55\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x97\x00\x17\x00\x18\x00\x19\x00\xba\x00\xa2\x00\x83\x00\x69\x00\x69\x00\xa3\x00\x3b\x00\x3c\x00\x50\x00\x51\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x46\x00\x18\x00\x19\x00\x53\x00\xc0\x00\x47\x00\xb6\x00\x48\x00\xc2\x00\xb9\x00\x69\x00\xaf\x00\xb0\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x17\x00\x60\x00\x47\x00\x79\x00\x48\x00\xba\x00\xa5\x00\xab\x00\x82\x00\x90\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x93\x00\x96\x00\x47\x00\x97\x00\x48\x00\xbe\x00\x17\x00\x99\x00\x5e\x00\x17\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x62\x00\xff\xff\x47\x00\xff\xff\x48\x00\xb4\x00\x6a\x00\xff\xff\x6c\x00\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x17\x00\x79\x00\x47\x00\x38\x00\x48\x00\x9f\x00\xff\xff\x17\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x00\x00\x00\x00\x47\x00\x00\x00\x48\x00\xa0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x46\x00\x18\x00\x19\x00\x00\x00\x00\x00\x47\x00\x00\x00\x48\x00\x57\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x38\x00\x00\x00\x00\x00\x00\x00\x7b\x00\x3d\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x6d\x00\x46\x00\x18\x00\x19\x00\x00\x00\x00\x00\x47\x00\x00\x00\x48\x00\x49\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x4a\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xbd\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xb7\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xb0\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xa3\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xa9\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x7f\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x93\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x94\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x59\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x5a\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x5c\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x6d\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x2d\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x99\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x2e\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x83\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x2f\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x84\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x85\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x30\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x86\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x87\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x88\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x89\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x7c\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x32\x00\x41\x00\x00\x00\x17\x00\x18\x00\x19\x00\x00\x00\x42\x00\x00\x00\x43\x00\x00\x00\x00\x00\x44\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x7a\x00\x45\x00\x17\x00\x18\x00\x19\x00\x00\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x8a\x00\x00\x00\x00\x00\x1a\x00\x1b\x00\x1c\x00\x8b\x00\x1a\x00\x1b\x00\x1c\x00\x33\x00\x17\x00\x18\x00\x19\x00\x17\x00\x18\x00\x19\x00\x17\x00\x18\x00\x19\x00\x17\x00\x18\x00\x19\x00\x00\x00\x1a\x00\x1b\x00\x8c\x00\x1a\x00\x1b\x00\x8d\x00\x1a\x00\x1b\x00\x34\x00\x1a\x00\x35\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (21, 95) [
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95)
	]

happy_n_terms = 52 :: Int
happy_n_nonterms = 24 :: Int

happyReduce_21 = happySpecReduce_1  0# happyReduction_21
happyReduction_21 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn24
		 (Ident happy_var_1
	)}

happyReduce_22 = happySpecReduce_1  1# happyReduction_22
happyReduction_22 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn25
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_23 = happySpecReduce_1  2# happyReduction_23
happyReduction_23 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TL happy_var_1)) -> 
	happyIn26
		 (happy_var_1
	)}

happyReduce_24 = happySpecReduce_1  3# happyReduction_24
happyReduction_24 happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	happyIn27
		 (AbsMy.PDefs (reverse happy_var_1)
	)}

happyReduce_25 = happySpecReduce_0  4# happyReduction_25
happyReduction_25  =  happyIn28
		 ([]
	)

happyReduce_26 = happySpecReduce_2  4# happyReduction_26
happyReduction_26 happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_2 of { happy_var_2 -> 
	happyIn28
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_27 = happyReduce 4# 5# happyReduction_27
happyReduction_27 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_2 of { happy_var_2 -> 
	case happyOut46 happy_x_4 of { happy_var_4 -> 
	happyIn29
		 (AbsMy.DField happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_28 = happySpecReduce_0  6# happyReduction_28
happyReduction_28  =  happyIn30
		 ([]
	)

happyReduce_29 = happySpecReduce_2  6# happyReduction_29
happyReduction_29 happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn30
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_30 = happySpecReduce_1  7# happyReduction_30
happyReduction_30 happy_x_1
	 =  happyIn31
		 (AbsMy.MVal
	)

happyReduce_31 = happySpecReduce_1  7# happyReduction_31
happyReduction_31 happy_x_1
	 =  happyIn31
		 (AbsMy.MVar
	)

happyReduce_32 = happyReduce 4# 8# happyReduction_32
happyReduction_32 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 (AbsMy.SEAsign happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_33 = happyReduce 7# 8# happyReduction_33
happyReduction_33 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	case happyOut46 happy_x_6 of { happy_var_6 -> 
	happyIn32
		 (AbsMy.SArrAsign happy_var_1 happy_var_3 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_34 = happySpecReduce_2  8# happyReduction_34
happyReduction_34 happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (AbsMy.SExp happy_var_1
	)}

happyReduce_35 = happySpecReduce_2  8# happyReduction_35
happyReduction_35 happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (AbsMy.SDef happy_var_1
	)}

happyReduce_36 = happySpecReduce_3  8# happyReduction_36
happyReduction_36 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (AbsMy.SInc happy_var_1
	)}

happyReduce_37 = happySpecReduce_3  8# happyReduction_37
happyReduction_37 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (AbsMy.SDec happy_var_1
	)}

happyReduce_38 = happySpecReduce_3  8# happyReduction_38
happyReduction_38 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_2 of { happy_var_2 -> 
	happyIn32
		 (AbsMy.SReturnE happy_var_2
	)}

happyReduce_39 = happySpecReduce_2  8# happyReduction_39
happyReduction_39 happy_x_2
	happy_x_1
	 =  happyIn32
		 (AbsMy.SReturn
	)

happyReduce_40 = happyReduce 4# 8# happyReduction_40
happyReduction_40 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut46 happy_x_2 of { happy_var_2 -> 
	case happyOut32 happy_x_4 of { happy_var_4 -> 
	happyIn32
		 (AbsMy.SWhile happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_41 = happyReduce 9# 8# happyReduction_41
happyReduction_41 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_3 of { happy_var_3 -> 
	case happyOut46 happy_x_5 of { happy_var_5 -> 
	case happyOut46 happy_x_7 of { happy_var_7 -> 
	case happyOut32 happy_x_9 of { happy_var_9 -> 
	happyIn32
		 (AbsMy.SFor happy_var_3 happy_var_5 happy_var_7 happy_var_9
	) `HappyStk` happyRest}}}}

happyReduce_42 = happyReduce 7# 8# happyReduction_42
happyReduction_42 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_3 of { happy_var_3 -> 
	case happyOut24 happy_x_5 of { happy_var_5 -> 
	case happyOut32 happy_x_7 of { happy_var_7 -> 
	happyIn32
		 (AbsMy.SForEach happy_var_3 happy_var_5 happy_var_7
	) `HappyStk` happyRest}}}

happyReduce_43 = happySpecReduce_3  8# happyReduction_43
happyReduction_43 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_2 of { happy_var_2 -> 
	happyIn32
		 (AbsMy.SBlock (reverse happy_var_2)
	)}

happyReduce_44 = happyReduce 5# 8# happyReduction_44
happyReduction_44 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut46 happy_x_2 of { happy_var_2 -> 
	case happyOut32 happy_x_4 of { happy_var_4 -> 
	happyIn32
		 (AbsMy.SIf happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_45 = happyReduce 7# 8# happyReduction_45
happyReduction_45 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut46 happy_x_2 of { happy_var_2 -> 
	case happyOut32 happy_x_4 of { happy_var_4 -> 
	case happyOut32 happy_x_6 of { happy_var_6 -> 
	happyIn32
		 (AbsMy.SIfElse happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_46 = happySpecReduce_1  9# happyReduction_46
happyReduction_46 happy_x_1
	 =  happyIn33
		 (AbsMy.Tbool
	)

happyReduce_47 = happySpecReduce_1  9# happyReduction_47
happyReduction_47 happy_x_1
	 =  happyIn33
		 (AbsMy.Tint
	)

happyReduce_48 = happySpecReduce_1  9# happyReduction_48
happyReduction_48 happy_x_1
	 =  happyIn33
		 (AbsMy.Tvoid
	)

happyReduce_49 = happySpecReduce_1  9# happyReduction_49
happyReduction_49 happy_x_1
	 =  happyIn33
		 (AbsMy.TString
	)

happyReduce_50 = happyReduce 8# 9# happyReduction_50
happyReduction_50 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut34 happy_x_4 of { happy_var_4 -> 
	case happyOut33 happy_x_7 of { happy_var_7 -> 
	happyIn33
		 (AbsMy.TFun happy_var_4 happy_var_7
	) `HappyStk` happyRest}}

happyReduce_51 = happySpecReduce_2  9# happyReduction_51
happyReduction_51 happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (AbsMy.TArray happy_var_1
	)}

happyReduce_52 = happySpecReduce_0  10# happyReduction_52
happyReduction_52  =  happyIn34
		 ([]
	)

happyReduce_53 = happySpecReduce_1  10# happyReduction_53
happyReduction_53 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn34
		 ((:[]) happy_var_1
	)}

happyReduce_54 = happySpecReduce_3  10# happyReduction_54
happyReduction_54 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut34 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_55 = happySpecReduce_0  11# happyReduction_55
happyReduction_55  =  happyIn35
		 ([]
	)

happyReduce_56 = happySpecReduce_1  11# happyReduction_56
happyReduction_56 happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	happyIn35
		 ((:[]) happy_var_1
	)}

happyReduce_57 = happySpecReduce_3  11# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	case happyOut35 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_58 = happyReduce 4# 12# happyReduction_58
happyReduction_58 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_2 of { happy_var_2 -> 
	case happyOut33 happy_x_4 of { happy_var_4 -> 
	happyIn36
		 (AbsMy.ADecl happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_59 = happySpecReduce_3  13# happyReduction_59
happyReduction_59 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_2 of { happy_var_2 -> 
	happyIn37
		 (happy_var_2
	)}

happyReduce_60 = happySpecReduce_1  14# happyReduction_60
happyReduction_60 happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsMy.EIdent happy_var_1
	)}

happyReduce_61 = happySpecReduce_1  14# happyReduction_61
happyReduction_61 happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsMy.EInt happy_var_1
	)}

happyReduce_62 = happySpecReduce_1  14# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsMy.EString happy_var_1
	)}

happyReduce_63 = happySpecReduce_1  14# happyReduction_63
happyReduction_63 happy_x_1
	 =  happyIn38
		 (AbsMy.ETrue
	)

happyReduce_64 = happySpecReduce_1  14# happyReduction_64
happyReduction_64 happy_x_1
	 =  happyIn38
		 (AbsMy.EFalse
	)

happyReduce_65 = happyReduce 7# 14# happyReduction_65
happyReduction_65 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut35 happy_x_2 of { happy_var_2 -> 
	case happyOut33 happy_x_5 of { happy_var_5 -> 
	case happyOut32 happy_x_7 of { happy_var_7 -> 
	happyIn38
		 (AbsMy.EFun happy_var_2 happy_var_5 happy_var_7
	) `HappyStk` happyRest}}}

happyReduce_66 = happyReduce 4# 14# happyReduction_66
happyReduction_66 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut47 happy_x_3 of { happy_var_3 -> 
	happyIn38
		 (AbsMy.EAppFun happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_67 = happyReduce 5# 14# happyReduction_67
happyReduction_67 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut33 happy_x_2 of { happy_var_2 -> 
	case happyOut46 happy_x_4 of { happy_var_4 -> 
	happyIn38
		 (AbsMy.EArrIni happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_68 = happySpecReduce_2  14# happyReduction_68
happyReduction_68 happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsMy.EArrLen happy_var_1
	)}

happyReduce_69 = happyReduce 4# 14# happyReduction_69
happyReduction_69 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	happyIn38
		 (AbsMy.EArrAcc happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_70 = happySpecReduce_1  14# happyReduction_70
happyReduction_70 happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (happy_var_1
	)}

happyReduce_71 = happySpecReduce_2  15# happyReduction_71
happyReduction_71 happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_2 of { happy_var_2 -> 
	happyIn39
		 (AbsMy.ENeg happy_var_2
	)}

happyReduce_72 = happySpecReduce_1  15# happyReduction_72
happyReduction_72 happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (happy_var_1
	)}

happyReduce_73 = happySpecReduce_3  16# happyReduction_73
happyReduction_73 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOut39 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (AbsMy.EMul happy_var_1 happy_var_3
	)}}

happyReduce_74 = happySpecReduce_3  16# happyReduction_74
happyReduction_74 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOut39 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (AbsMy.EDiv happy_var_1 happy_var_3
	)}}

happyReduce_75 = happySpecReduce_1  16# happyReduction_75
happyReduction_75 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 (happy_var_1
	)}

happyReduce_76 = happySpecReduce_3  17# happyReduction_76
happyReduction_76 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn41
		 (AbsMy.EPlus happy_var_1 happy_var_3
	)}}

happyReduce_77 = happySpecReduce_3  17# happyReduction_77
happyReduction_77 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn41
		 (AbsMy.EMinus happy_var_1 happy_var_3
	)}}

happyReduce_78 = happySpecReduce_1  17# happyReduction_78
happyReduction_78 happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (happy_var_1
	)}

happyReduce_79 = happySpecReduce_2  18# happyReduction_79
happyReduction_79 happy_x_2
	happy_x_1
	 =  case happyOut41 happy_x_2 of { happy_var_2 -> 
	happyIn42
		 (AbsMy.ENot happy_var_2
	)}

happyReduce_80 = happySpecReduce_1  18# happyReduction_80
happyReduction_80 happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (happy_var_1
	)}

happyReduce_81 = happySpecReduce_3  19# happyReduction_81
happyReduction_81 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (AbsMy.ELt happy_var_1 happy_var_3
	)}}

happyReduce_82 = happySpecReduce_3  19# happyReduction_82
happyReduction_82 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (AbsMy.EGt happy_var_1 happy_var_3
	)}}

happyReduce_83 = happySpecReduce_3  19# happyReduction_83
happyReduction_83 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (AbsMy.EGtEq happy_var_1 happy_var_3
	)}}

happyReduce_84 = happySpecReduce_3  19# happyReduction_84
happyReduction_84 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (AbsMy.ELtEq happy_var_1 happy_var_3
	)}}

happyReduce_85 = happySpecReduce_1  19# happyReduction_85
happyReduction_85 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (happy_var_1
	)}

happyReduce_86 = happySpecReduce_3  20# happyReduction_86
happyReduction_86 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (AbsMy.EEq happy_var_1 happy_var_3
	)}}

happyReduce_87 = happySpecReduce_3  20# happyReduction_87
happyReduction_87 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (AbsMy.ENeq happy_var_1 happy_var_3
	)}}

happyReduce_88 = happySpecReduce_1  20# happyReduction_88
happyReduction_88 happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (happy_var_1
	)}

happyReduce_89 = happySpecReduce_3  21# happyReduction_89
happyReduction_89 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn45
		 (AbsMy.EAnd happy_var_1 happy_var_3
	)}}

happyReduce_90 = happySpecReduce_1  21# happyReduction_90
happyReduction_90 happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn45
		 (happy_var_1
	)}

happyReduce_91 = happySpecReduce_3  22# happyReduction_91
happyReduction_91 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	happyIn46
		 (AbsMy.EOr happy_var_1 happy_var_3
	)}}

happyReduce_92 = happySpecReduce_1  22# happyReduction_92
happyReduction_92 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 (happy_var_1
	)}

happyReduce_93 = happySpecReduce_0  23# happyReduction_93
happyReduction_93  =  happyIn47
		 ([]
	)

happyReduce_94 = happySpecReduce_1  23# happyReduction_94
happyReduction_94 happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	happyIn47
		 ((:[]) happy_var_1
	)}

happyReduce_95 = happySpecReduce_3  23# happyReduction_95
happyReduction_95 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	case happyOut47 happy_x_3 of { happy_var_3 -> 
	happyIn47
		 ((:) happy_var_1 happy_var_3
	)}}

happyNewToken action sts stk [] =
	happyDoAction 51# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TS _ 44) -> cont 44#;
	PT _ (TS _ 45) -> cont 45#;
	PT _ (TS _ 46) -> cont 46#;
	PT _ (TS _ 47) -> cont 47#;
	PT _ (TV happy_dollar_dollar) -> cont 48#;
	PT _ (TI happy_dollar_dollar) -> cont 49#;
	PT _ (TL happy_dollar_dollar) -> cont 50#;
	_ -> happyError' (tk:tks)
	}

happyError_ 51# tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pProgram tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut27 x))

pListDef tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut28 x))

pDef tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut29 x))

pListStm tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut30 x))

pMod tks = happySomeParser where
  happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (happyOut31 x))

pStm tks = happySomeParser where
  happySomeParser = happyThen (happyParse 5# tks) (\x -> happyReturn (happyOut32 x))

pType tks = happySomeParser where
  happySomeParser = happyThen (happyParse 6# tks) (\x -> happyReturn (happyOut33 x))

pListType tks = happySomeParser where
  happySomeParser = happyThen (happyParse 7# tks) (\x -> happyReturn (happyOut34 x))

pListArg tks = happySomeParser where
  happySomeParser = happyThen (happyParse 8# tks) (\x -> happyReturn (happyOut35 x))

pArg tks = happySomeParser where
  happySomeParser = happyThen (happyParse 9# tks) (\x -> happyReturn (happyOut36 x))

pExp9 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 10# tks) (\x -> happyReturn (happyOut37 x))

pExp8 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 11# tks) (\x -> happyReturn (happyOut38 x))

pExp7 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 12# tks) (\x -> happyReturn (happyOut39 x))

pExp6 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 13# tks) (\x -> happyReturn (happyOut40 x))

pExp5 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 14# tks) (\x -> happyReturn (happyOut41 x))

pExp4 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 15# tks) (\x -> happyReturn (happyOut42 x))

pExp3 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 16# tks) (\x -> happyReturn (happyOut43 x))

pExp2 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 17# tks) (\x -> happyReturn (happyOut44 x))

pExp1 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 18# tks) (\x -> happyReturn (happyOut45 x))

pExp tks = happySomeParser where
  happySomeParser = happyThen (happyParse 19# tks) (\x -> happyReturn (happyOut46 x))

pListExp tks = happySomeParser where
  happySomeParser = happyThen (happyParse 20# tks) (\x -> happyReturn (happyOut47 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 11 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4










































{-# LINE 11 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}

















{-# LINE 11 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates/GenericTemplate.hs" #-}





-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif
{-# LINE 46 "templates/GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList





{-# LINE 67 "templates/GenericTemplate.hs" #-}

{-# LINE 77 "templates/GenericTemplate.hs" #-}

{-# LINE 86 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}


          case action of
                0#           -> {- nothing -}
                                     happyFail i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}


                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st


indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 170 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
