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

(** val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT **)

let compare_spec x = x.compare_spec

type a (* AXIOM TO BE REALIZED *)

(** val ordA : a ordered **)

let ordA =
  failwith "AXIOM TO BE REALIZED"

type wavltree =
| Node of bool * a * wavltree * wavltree
| Missing

type findResult =
| Found
| NotFound

(** val find : a -> wavltree -> findResult **)

let rec find x = function
| Node (_, d, lw, rw) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x lw
   | CompGtT -> find x rw)
| Missing -> NotFound

(** val setgap : wavltree -> bool -> wavltree **)

let setgap w og =
  match w with
  | Node (_, d, lw, rw) -> Node (og, d, lw, rw)
  | Missing -> Missing

(** val getgap : wavltree -> bool **)

let getgap = function
| Node (g0, _, _, _) -> g0
| Missing -> false

(** val isgap : wavltree -> bool -> bool **)

let isgap w g' =
  match w with
  | Node (g0, _, _, _) -> (=) g' g0
  | Missing -> false

(** val isMissing : wavltree -> bool **)

let isMissing = function
| Node (_, _, _, _) -> false
| Missing -> true

(** val irot1 : wavltree -> a -> wavltree -> bool -> wavltree **)

let irot1 lw x rw g =
  match lw with
  | Node (_, d, lw0, rw0) ->
    (match rw0 with
     | Node (g1, d0, lw1, rw1) ->
       if g1
       then Node (g, d, lw0, (Node (false, x, (setgap rw0 false), (setgap rw false))))
       else Node (g, d0, (Node (false, d, (setgap lw0 false), lw1)), (Node (false, x, rw1, (setgap rw false))))
     | Missing -> Node (g, d, lw0, (Node (false, x, Missing, (setgap rw false)))))
  | Missing -> assert false (* absurd case *)

(** val irot2 : wavltree -> a -> wavltree -> bool -> wavltree **)

let irot2 lw x rw g =
  match rw with
  | Node (_, d, lw0, rw0) ->
    (match lw0 with
     | Node (g1, d0, lw1, rw1) ->
       if g1
       then Node (g, d, (Node (false, x, (setgap lw false), (setgap lw0 false))), rw0)
       else Node (g, d0, (Node (false, x, (setgap lw false), lw1)), (Node (false, d, rw1, (setgap rw0 false))))
     | Missing -> Node (g, d, (Node (false, x, (setgap lw false), Missing)), rw0))
  | Missing -> assert false (* absurd case *)

type insertedHow =
| ISameK
| IWasMissing
| IHigherK

type insertResult =
| Inserted of wavltree * insertedHow
| FoundByInsert

(** val insert : a -> wavltree -> insertResult **)

let rec insert x = function
| Node (g0, d, lw, rw) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x lw with
      | Inserted (ow, insertedHow0) ->
        (match insertedHow0 with
         | ISameK -> Inserted ((Node (g0, d, ow, rw)), ISameK)
         | IWasMissing ->
           if isMissing rw
           then Inserted ((Node (false, d, ow, Missing)), IHigherK)
           else Inserted ((Node (g0, d, ow, rw)), ISameK)
         | IHigherK ->
           if getgap lw
           then Inserted ((Node (g0, d, ow, rw)), ISameK)
           else if isgap rw false
                then Inserted ((Node (false, d, ow, (setgap rw true))), IHigherK)
                else Inserted ((irot1 ow d rw g0), ISameK))
      | FoundByInsert -> FoundByInsert)
   | CompGtT ->
     (match insert x rw with
      | Inserted (ow, insertedHow0) ->
        (match insertedHow0 with
         | ISameK -> Inserted ((Node (g0, d, lw, ow)), ISameK)
         | IWasMissing ->
           if isMissing lw
           then Inserted ((Node (false, d, Missing, ow)), IHigherK)
           else Inserted ((Node (g0, d, lw, ow)), ISameK)
         | IHigherK ->
           if getgap rw
           then Inserted ((Node (g0, d, lw, ow)), ISameK)
           else if isgap lw false
                then Inserted ((Node (false, d, (setgap lw true), ow)), IHigherK)
                else Inserted ((irot2 lw d ow g0), ISameK))
      | FoundByInsert -> FoundByInsert))
| Missing -> Inserted ((Node (false, x, Missing, Missing)), IWasMissing)

type tryLoweringResult =
| TLlowered of wavltree
| TLtooLow

(** val tryLowering : wavltree -> tryLoweringResult **)

let tryLowering = function
| Node (g0, d, lw, rw) ->
  if isgap lw true
  then if isgap rw true then TLlowered (Node (g0, d, (setgap lw false), (setgap rw false))) else TLtooLow
  else TLtooLow
| Missing -> TLtooLow

type deletedHow =
| DSameK
| DLowerK

(** val drot1 : wavltree -> a -> wavltree -> bool -> ( * ) **)

let drot1 lw x rw g =
  match rw with
  | Node (_, d, lw0, rw0) ->
    (match lw0 with
     | Node (_, d0, lw1, rw1) ->
       if isgap rw0 false
       then (DSameK, (Node (g, d, (Node (false, x, lw, lw0)), (setgap rw0 true))))
       else (DSameK, (Node (g, d0, (Node (true, x, (setgap lw false), lw1)), (Node (true, d, rw1,
              (setgap rw0 false))))))
     | Missing -> (DSameK, (Node (g, d, (Node (true, x, (setgap lw false), Missing)), (setgap rw0 true)))))
  | Missing -> assert false (* absurd case *)

(** val drot2 : wavltree -> a -> wavltree -> bool -> ( * ) **)

let drot2 lw x rw g =
  match lw with
  | Node (_, d, lw0, rw0) ->
    (match rw0 with
     | Node (_, d0, lw1, rw1) ->
       if isgap lw0 false
       then (DSameK, (Node (g, d, (setgap lw0 true), (Node (false, x, rw0, rw)))))
       else (DSameK, (Node (g, d0, (Node (true, d, (setgap lw0 false), lw1)), (Node (true, x, rw1,
              (setgap rw false))))))
     | Missing -> (DSameK, (Node (g, d, (setgap lw0 true), (Node (true, x, Missing, (setgap rw false)))))))
  | Missing -> assert false (* absurd case *)

(** val delmin : wavltree -> ( * ) **)

let rec delmin = function
| Node (g0, d, lw, rw) ->
  if isMissing lw
  then (d, (DLowerK, (setgap rw true)))
  else let (min, dp) = delmin lw in
       let (dh, ow) = dp in
       (match dh with
        | DSameK -> (min, (DSameK, (Node (g0, d, ow, rw))))
        | DLowerK ->
          if isgap rw false
          then if isgap lw true
               then (match tryLowering rw with
                     | TLlowered ow0 -> (min, (DLowerK, (Node (true, d, ow, ow0))))
                     | TLtooLow -> (min, (drot1 ow d rw g0)))
               else (min, (DSameK, (Node (g0, d, ow, rw))))
          else (min, (DLowerK, (Node (true, d, (setgap ow (getgap lw)), (setgap rw false))))))
| Missing -> assert false (* absurd case *)

(** val delmax : wavltree -> ( * ) **)

let rec delmax = function
| Node (g0, d, lw, rw) ->
  if isMissing rw
  then (d, (DLowerK, (setgap lw true)))
  else let (max, dp) = delmax rw in
       let (dh, ow) = dp in
       (match dh with
        | DSameK -> (max, (DSameK, (Node (g0, d, lw, ow))))
        | DLowerK ->
          if isgap lw false
          then if isgap rw true
               then (match tryLowering lw with
                     | TLlowered ow0 -> (max, (DLowerK, (Node (true, d, ow0, ow))))
                     | TLtooLow -> (max, (drot2 lw d ow g0)))
               else (max, (DSameK, (Node (g0, d, lw, ow))))
          else (max, (DLowerK, (Node (true, d, (setgap lw false), (setgap ow (getgap rw)))))))
| Missing -> assert false (* absurd case *)

type deleteResult =
| Deleted of ( * )
| DNotFound

(** val delete : a -> wavltree -> deleteResult **)

let rec delete x = function
| Node (g0, d, lw, rw) ->
  (match ordA.compare_spec x d with
   | CompEqT ->
     if isMissing lw
     then Deleted (DLowerK, (setgap rw true))
     else if isMissing rw
          then Deleted (DLowerK, (setgap lw true))
          else if getgap lw
               then let (min, dp) = delmin rw in
                    let (dh, ow) = dp in
                    (match dh with
                     | DSameK -> Deleted (DSameK, (Node (g0, min, lw, ow)))
                     | DLowerK -> Deleted (DLowerK, (Node (true, min, (setgap lw false), (setgap ow (getgap rw))))))
               else let (max, dp) = delmax lw in let (_, ow) = dp in Deleted (DSameK, (Node (g0, max, ow, rw)))
   | CompLtT ->
     (match delete x lw with
      | Deleted dp ->
        let (dh, ow) = dp in
        (match dh with
         | DSameK -> Deleted (DSameK, (Node (g0, d, ow, rw)))
         | DLowerK ->
           if getgap lw
           then if getgap rw
                then Deleted (DLowerK, (Node (true, d, ow, (setgap rw false))))
                else (match tryLowering rw with
                      | TLlowered ow0 -> Deleted (DLowerK, (Node (true, d, ow, ow0)))
                      | TLtooLow -> Deleted (drot1 ow d rw g0))
           else if isMissing rw
                then Deleted (DLowerK, (Node (true, d, (setgap ow false), Missing)))
                else Deleted (DSameK, (Node (g0, d, ow, rw))))
      | DNotFound -> DNotFound)
   | CompGtT ->
     (match delete x rw with
      | Deleted dp ->
        let (dh, ow) = dp in
        (match dh with
         | DSameK -> Deleted (DSameK, (Node (g0, d, lw, ow)))
         | DLowerK ->
           if getgap rw
           then if getgap lw
                then Deleted (DLowerK, (Node (true, d, (setgap lw false), ow)))
                else (match tryLowering lw with
                      | TLlowered ow0 -> Deleted (DLowerK, (Node (true, d, ow0, ow)))
                      | TLtooLow -> Deleted (drot2 lw d ow g0))
           else if isMissing lw
                then Deleted (DLowerK, (Node (true, d, Missing, (setgap ow false))))
                else Deleted (DSameK, (Node (g0, d, lw, ow))))
      | DNotFound -> DNotFound))
| Missing -> DNotFound
