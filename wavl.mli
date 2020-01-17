
type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



type 'a ordered = { compare : ('a -> 'a -> comparison); compare_spec : ('a -> 'a -> compareSpecT) }

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type wavltree =
| Node of bool * a * wavltree * wavltree
| Missing

type findResult =
| Found
| NotFound

val find : a -> wavltree -> findResult

val setgap : wavltree -> bool -> wavltree

val getgap : wavltree -> bool

val isgap : wavltree -> bool -> bool

val isMissing : wavltree -> bool

val irot1 : wavltree -> a -> wavltree -> bool -> wavltree

val irot2 : wavltree -> a -> wavltree -> bool -> wavltree

type insertedHow =
| ISameK
| IWasMissing
| IHigherK

type insertResult =
| Inserted of wavltree * insertedHow
| FoundByInsert

val insert : a -> wavltree -> insertResult

type tryLoweringResult =
| TLlowered of wavltree
| TLtooLow

val tryLowering : wavltree -> tryLoweringResult

type deletedHow =
| DSameK
| DLowerK

val drot1 : wavltree -> a -> wavltree -> bool -> ( * )

val drot2 : wavltree -> a -> wavltree -> bool -> ( * )

val delmin : wavltree -> ( * )

val delmax : wavltree -> ( * )

type deleteResult =
| Deleted of ( * )
| DNotFound

val delete : a -> wavltree -> deleteResult
