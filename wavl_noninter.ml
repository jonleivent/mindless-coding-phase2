
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
| Node (g, _, _, _) -> g
| Missing -> false

(** val isgap : wavltree -> bool -> bool **)

let isgap w g' =
  match w with
  | Node (g, _, _, _) -> (=) g' g
  | Missing -> false

(** val isMissing : wavltree -> bool **)

let isMissing = function
| Node (_, _, _, _) -> false
| Missing -> true

(** val irot1 : wavltree -> a -> wavltree -> bool -> wavltree **)

let irot1 lw x rw g =
  match lw with
  | Node (_, d, llw, lrw) ->
    (match lrw with
     | Node (g0, d0, lw0, rw0) ->
       if g0
       then Node (g, d, llw, (Node (false, x, (setgap lrw false), (setgap rw false))))
       else Node (g, d0, (Node (false, d, (setgap llw false), lw0)), (Node (false, x, rw0, (setgap rw false))))
     | Missing -> Node (g, d, llw, (Node (false, x, Missing, (setgap rw false)))))
  | Missing -> assert false (* absurd case *)

(** val irot2 : wavltree -> a -> wavltree -> bool -> wavltree **)

let irot2 lw x rw g =
  match rw with
  | Node (_, d, rlw, rrw) ->
    (match rlw with
     | Node (g0, d0, lw0, rw0) ->
       if g0
       then Node (g, d, (Node (false, x, (setgap lw false), (setgap rlw false))), rrw)
       else Node (g, d0, (Node (false, x, (setgap lw false), lw0)), (Node (false, d, rw0, (setgap rrw false))))
     | Missing -> Node (g, d, (Node (false, x, (setgap lw false), Missing)), rrw))
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
           if isgap lw true
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
           if isgap rw true
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
  | Node (_, d, rlw, rrw) ->
    (match rlw with
     | Node (_, d0, lw0, rw0) ->
       if isgap rrw false
       then (DSameK, (Node (g, d, (Node (false, x, lw, rlw)), (setgap rrw true))))
       else (DSameK, (Node (g, d0, (Node (true, x, (setgap lw false), lw0)), (Node (true, d, rw0,
              (setgap rrw false))))))
     | Missing -> (DSameK, (Node (g, d, (Node (true, x, (setgap lw false), Missing)), (setgap rrw true)))))
  | Missing -> assert false (* absurd case *)

(** val drot2 : wavltree -> a -> wavltree -> bool -> ( * ) **)

let drot2 lw x rw g =
  match lw with
  | Node (_, d, llw, lrw) ->
    (match lrw with
     | Node (_, d0, lw0, rw0) ->
       if isgap llw false
       then (DSameK, (Node (g, d, (setgap llw true), (Node (false, x, lrw, rw)))))
       else (DSameK, (Node (g, d0, (Node (true, d, (setgap llw false), lw0)), (Node (true, x, rw0,
              (setgap rw false))))))
     | Missing -> (DSameK, (Node (g, d, (setgap llw true), (Node (true, x, Missing, (setgap rw false)))))))
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
          else if isgap lw true
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
           if isgap lw true
           then if isgap rw true
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
           if isgap rw true
           then if isgap lw true
                then Deleted (DLowerK, (Node (true, d, (setgap lw false), ow)))
                else (match tryLowering lw with
                      | TLlowered ow0 -> Deleted (DLowerK, (Node (true, d, ow0, ow)))
                      | TLtooLow -> Deleted (drot2 lw d ow g0))
           else if isMissing lw
                then Deleted (DLowerK, (Node (true, d, Missing, (setgap ow false))))
                else Deleted (DSameK, (Node (g0, d, lw, ow))))
      | DNotFound -> DNotFound))
| Missing -> DNotFound
