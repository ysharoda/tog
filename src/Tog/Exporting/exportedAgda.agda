module exportedAgda  where

  open import Agda.Builtin.Equality
  
  data Prod (A B  : Set )  : Set where
    
  module Carrier  where
    record Carrier (A  : Set )  : Set where
      constructor CarrierC
    
    record CarrierSig (AS  : Set )  : Set where
      constructor CarrierSigSigC
    
    record CarrierProd (AP  : Set )  : Set where
      constructor CarrierProdC
    
    record CarrierHom (A1 A2  : Set ) (Ca1  : (Carrier A1 )) (Ca2  : (Carrier A2 ))  : Set where
      constructor CarrierHomC
      field
        hom : A1 → A2
    record CarrierRelInterp (A1 A2  : Set ) (Ca1  : (Carrier A1 )) (Ca2  : (Carrier A2 ))  : Set₁ where
      constructor CarrierRelInterpC
      field
        interp : A1 → A2 → Set
  module Empty  where
    record Empty  : Set where
      constructor EmptyC
    
  module Magma  where
    record Magma (A  : Set )  : Set where
      constructor MagmaC
      field
        op : A  → A  → A 
    record MagmaSig (AS  : Set )  : Set where
      constructor MagmaSigSigC
      field
        opS : AS  → AS  → AS 
    record MagmaProd (AP  : Set )  : Set where
      constructor MagmaProdC
      field
        opP : (Prod AP AP ) → (Prod AP AP ) → (Prod AP AP )
 {-       
    record MagmaHom (A1 A2  : Set ) (Ma1  : (Magma A1 )) (Ma2  : (Magma A2 ))  : Set where
      constructor MagmaHomC
      field
        hom : A1 → A2
        pres-op : {x1  : A1} {x2  : A1}  → (hom ((op Ma1 ) x1 x2 ) ) ≡ ((op Ma2 ) (hom x1 ) (hom x2 ) )
   record MagmaRelInterp (A1 A2  : Set ) (Ma1  : (Magma A1 )) (Ma2  : (Magma A2 ))  : Set where
      constructor MagmaRelInterpC
      field
        interp : A1 → A2 → Set
        interp-op : {x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → (interp x1 y1 ) → (interp x2 y2 ) → (interp ((op Ma1 ) x1 x2 ) ((op Ma2 ) y1 y2 ) )
  module Pointed  where
    record Pointed (A  : Set )  : Set where
      constructor PointedC
      field
        e : A 
    record PointedSig (AS  : Set )  : Set where
      constructor PointedSigSigC
      field
        eS : AS 
    record PointedProd (AP  : Set )  : Set where
      constructor PointedProdC
      field
        eP : (Prod AP AP )
    record PointedHom (A1 A2  : Set ) (Po1  : (Pointed A1 )) (Po2  : (Pointed A2 ))  : Set where
      constructor PointedHomC
      field
        hom : A1 → A2
        pres-e :   (hom (e Po1 )  ) ≡ (e Po2 ) 
    record PointedRelInterp (A1 A2  : Set ) (Po1  : (Pointed A1 )) (Po2  : (Pointed A2 ))  : Set where
      constructor PointedRelInterpC
      field
        interp : A1 → A2 → Set
        interp-e :   (interp (e Po1 )  (e Po2 )  )
  module PointedMagma  where
    record PointedMagma (A  : Set )  : Set where
      constructor PointedMagmaC
      field
        e : A 
        op : A  → A  → A 
    record PointedMagmaSig (AS  : Set )  : Set where
      constructor PointedMagmaSigSigC
      field
        eS : AS 
        opS : AS  → AS  → AS 
    record PointedMagmaProd (AP  : Set )  : Set where
      constructor PointedMagmaProdC
      field
        eP : (Prod AP AP )
        opP : (Prod AP AP ) → (Prod AP AP ) → (Prod AP AP )
    record PointedMagmaHom (A1 A2  : Set ) (Po1  : (PointedMagma A1 )) (Po2  : (PointedMagma A2 ))  : Set where
      constructor PointedMagmaHomC
      field
        hom : A1 → A2
        pres-e :   (hom (e Po1 )  ) ≡ (e Po2 ) 
        pres-op : {x1  : A1} {x2  : A1}  → (hom ((op Po1 ) x1 x2 ) ) ≡ ((op Po2 ) (hom x1 ) (hom x2 ) )
    record PointedMagmaRelInterp (A1 A2  : Set ) (Po1  : (PointedMagma A1 )) (Po2  : (PointedMagma A2 ))  : Set where
      constructor PointedMagmaRelInterpC
      field
        interp : A1 → A2 → Set
        interp-e :   (interp (e Po1 )  (e Po2 )  )
        interp-op : {x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → (interp x1 y1 ) → (interp x2 y2 ) → (interp ((op Po1 ) x1 x2 ) ((op Po2 ) y1 y2 ) )
-}
