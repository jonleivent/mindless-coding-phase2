type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)



type 'a eqDec = 'a -> 'a -> bool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison); compare_spec : ('a -> 'a -> compareSpecT) }

val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type wavltree =
| Missing
| Node of bool * wavltree * a * wavltree

val isMissing : wavltree -> bool

type findResult =
| Found
| NotFound

val find : a -> wavltree -> findResult

val setgap : wavltree -> bool -> wavltree

val getgap : wavltree -> bool

val gofis : wavltree -> bool -> bool

val rot1 : wavltree -> a -> wavltree -> bool -> wavltree

val rot2 : wavltree -> a -> wavltree -> bool -> wavltree

type insertedHow =
| ISameK
| IWasMissing
| IHigherK

type insertResult =
| FoundByInsert
| Inserted of wavltree * insertedHow

val insert : a -> wavltree -> insertResult

type tryLoweringResult =
| TLtooLow
| TLlowered of wavltree

val tryLowering : wavltree -> tryLoweringResult

type deletedHow =
| DSameK
| DLowerK

val drot1 : wavltree -> a -> wavltree -> bool -> ( * )

val drot2 : wavltree -> a -> wavltree -> bool -> ( * )

type delminResult =
| NoMin
| MinDeleted of a * ( * )

val delmin : wavltree -> delminResult

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

val delmax : wavltree -> delmaxResult

type deleteResult =
| Deleted of ( * )
| DNotFound

val delete : a -> wavltree -> deleteResult
