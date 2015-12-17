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
| Missing
| Node of bool * wavltree * a * wavltree

(** val isMissing : wavltree -> bool **)

let isMissing = function
| Missing -> true
| Node (_, _, _, _) -> false

type findResult =
| Found
| NotFound

(** val find : a -> wavltree -> findResult **)

let rec find x = function
| Missing -> NotFound
| Node (_, lc, d, rc) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x lc
   | CompGtT -> find x rc)

(** val setgap : wavltree -> bool -> wavltree **)

let setgap t g =
  match t with
  | Missing -> Missing
  | Node (_, lc, d, rc) -> Node (g, lc, d, rc)

(** val getgap : wavltree -> bool **)

let getgap = function
| Missing -> false
| Node (ug, _, _, _) -> ug

(** val gofis : wavltree -> bool -> bool **)

let gofis t ug =
  match t with
  | Missing -> false
  | Node (ug0, _, _, _) -> if ug then if ug0 then true else false else if ug0 then false else true

(** val rot1 : wavltree -> a -> wavltree -> bool -> wavltree **)

let rot1 lt x rt g =
  match lt with
  | Missing -> assert false (* absurd case *)
  | Node (_, lc, d, rc) ->
    (match rc with
     | Missing -> Node (g, lc, d, (Node (false, Missing, x, (setgap rt false))))
     | Node (ug0, lc0, d0, rc0) ->
       if ug0
       then Node (g, lc, d, (Node (false, (Node (false, lc0, d0, rc0)), x, (setgap rt false))))
       else Node (g, (Node (false, (setgap lc false), d, lc0)), d0, (Node (false, rc0, x, (setgap rt false)))))

(** val rot2 : wavltree -> a -> wavltree -> bool -> wavltree **)

let rot2 lt x rt g =
  match rt with
  | Missing -> assert false (* absurd case *)
  | Node (_, lc, d, rc) ->
    (match lc with
     | Missing -> Node (g, (Node (false, (setgap lt false), x, Missing)), d, rc)
     | Node (ug0, lc0, d0, rc0) ->
       if ug0
       then Node (g, (Node (false, (setgap lt false), x, (Node (false, lc0, d0, rc0)))), d, rc)
       else Node (g, (Node (false, (setgap lt false), x, lc0)), d0, (Node (false, rc0, d, (setgap rc false)))))

type insertedHow =
| ISameK
| IWasMissing
| IHigherK

type insertResult =
| FoundByInsert
| Inserted of wavltree * insertedHow

(** val insert : a -> wavltree -> insertResult **)

let rec insert x = function
| Missing -> Inserted ((Node (false, Missing, x, Missing)), IWasMissing)
| Node (ug, lc, d, rc) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x lc with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameK -> Inserted ((Node (ug, t0, d, rc)), ISameK)
         | IWasMissing ->
           if isMissing rc
           then Inserted ((Node (false, t0, d, Missing)), IHigherK)
           else Inserted ((Node (ug, t0, d, rc)), ISameK)
         | IHigherK ->
           if getgap lc
           then Inserted ((Node (ug, t0, d, rc)), ISameK)
           else if gofis rc false
                then Inserted ((Node (false, t0, d, (setgap rc true))), IHigherK)
                else Inserted ((rot1 t0 d rc ug), ISameK)))
   | CompGtT ->
     (match insert x rc with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameK -> Inserted ((Node (ug, lc, d, t0)), ISameK)
         | IWasMissing ->
           if isMissing lc
           then Inserted ((Node (false, Missing, d, t0)), IHigherK)
           else Inserted ((Node (ug, lc, d, t0)), ISameK)
         | IHigherK ->
           if getgap rc
           then Inserted ((Node (ug, lc, d, t0)), ISameK)
           else if gofis lc false
                then Inserted ((Node (false, (setgap lc true), d, t0)), IHigherK)
                else Inserted ((rot2 lc d t0 ug), ISameK))))

type tryLoweringResult =
| TLtooLow
| TLlowered of wavltree

(** val tryLowering : wavltree -> tryLoweringResult **)

let tryLowering = function
| Missing -> TLtooLow
| Node (ug, lc, d, rc) ->
  if gofis lc true
  then if gofis rc true then TLlowered (Node (ug, (setgap lc false), d, (setgap rc false))) else TLtooLow
  else TLtooLow

type deletedHow =
| DSameK
| DLowerK

(** val drot1 : wavltree -> a -> wavltree -> bool -> ( * ) **)

let drot1 t d t2 ug =
  match t2 with
  | Missing -> assert false (* absurd case *)
  | Node (_, lc, d0, rc) ->
    (match lc with
     | Missing -> ((Node (ug, (Node (true, (setgap t false), d, Missing)), d0, (setgap rc true))), DSameK)
     | Node (_, lc0, d1, rc0) ->
       if gofis rc false
       then ((Node (ug, (Node (false, t, d, lc)), d0, (setgap rc true))), DSameK)
       else ((Node (ug, (Node (true, (setgap t false), d, lc0)), d1, (Node (true, rc0, d0, (setgap rc false))))),
              DSameK))

(** val drot2 : wavltree -> a -> wavltree -> bool -> ( * ) **)

let drot2 t2 d t ug =
  match t2 with
  | Missing -> assert false (* absurd case *)
  | Node (_, lc, d0, rc) ->
    (match rc with
     | Missing -> ((Node (ug, (setgap lc true), d0, (Node (true, Missing, d, (setgap t false))))), DSameK)
     | Node (_, lc0, d1, rc0) ->
       if gofis lc false
       then ((Node (ug, (setgap lc true), d0, (Node (false, rc, d, t)))), DSameK)
       else ((Node (ug, (Node (true, (setgap lc false), d0, lc0)), d1, (Node (true, rc0, d, (setgap t false))))),
              DSameK))

type delminResult =
| NoMin
| MinDeleted of a * ( * )

(** val delmin : wavltree -> delminResult **)

let rec delmin = function
| Missing -> NoMin
| Node (ug, lc, d, rc) ->
  (match delmin lc with
   | NoMin -> MinDeleted (d, ((setgap rc true), DLowerK))
   | MinDeleted (min, dr) ->
     let (t, d0) = dr in
     (match d0 with
      | DSameK -> MinDeleted (min, ((Node (ug, t, d, rc)), DSameK))
      | DLowerK ->
        if gofis rc false
        then if gofis lc true
             then (match tryLowering rc with
                   | TLtooLow -> MinDeleted (min, (drot1 t d rc ug))
                   | TLlowered t' -> MinDeleted (min, ((Node (true, t, d, t')), DLowerK)))
             else MinDeleted (min, ((Node (ug, t, d, rc)), DSameK))
        else MinDeleted (min, ((Node (true, (setgap t (getgap lc)), d, (setgap rc false))), DLowerK))))

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

(** val delmax : wavltree -> delmaxResult **)

let rec delmax = function
| Missing -> NoMax
| Node (ug, lc, d, rc) ->
  (match delmax rc with
   | NoMax -> MaxDeleted (d, ((setgap lc true), DLowerK))
   | MaxDeleted (max, dr) ->
     let (t, d0) = dr in
     (match d0 with
      | DSameK -> MaxDeleted (max, ((Node (ug, lc, d, t)), DSameK))
      | DLowerK ->
        if gofis lc false
        then if gofis rc true
             then (match tryLowering lc with
                   | TLtooLow -> MaxDeleted (max, (drot2 lc d t ug))
                   | TLlowered t' -> MaxDeleted (max, ((Node (true, t', d, t)), DLowerK)))
             else MaxDeleted (max, ((Node (ug, lc, d, t)), DSameK))
        else MaxDeleted (max, ((Node (true, (setgap lc false), d, (setgap t (getgap rc)))), DLowerK))))

type deleteResult =
| Deleted of ( * )
| DNotFound

(** val delete : a -> wavltree -> deleteResult **)

let rec delete x = function
| Missing -> DNotFound
| Node (ug, lc, d, rc) ->
  (match ordA.compare_spec x d with
   | CompEqT ->
     if gofis rc false
     then let d0 = delmin rc in
          (match d0 with
           | NoMin -> Deleted (lc, DSameK)
           | MinDeleted (min, dr) ->
             let (t0, d1) = dr in
             (match d1 with
              | DSameK -> Deleted ((Node (ug, lc, min, t0)), DSameK)
              | DLowerK ->
                if isMissing lc
                then Deleted ((Node (true, Missing, min, (setgap t0 false))), DLowerK)
                else Deleted ((Node (ug, lc, min, t0)), DSameK)))
     else let d0 = delmax lc in
          (match d0 with
           | NoMax -> Deleted ((setgap rc true), DLowerK)
           | MaxDeleted (max, dr) ->
             let (t0, d1) = dr in
             (match d1 with
              | DSameK -> Deleted ((Node (ug, t0, max, rc)), DSameK)
              | DLowerK -> Deleted ((Node (true, (setgap t0 (getgap lc)), max, (setgap rc false))), DLowerK)))
   | CompLtT ->
     (match delete x lc with
      | Deleted dr ->
        let (t0, d0) = dr in
        (match d0 with
         | DSameK -> Deleted ((Node (ug, t0, d, rc)), DSameK)
         | DLowerK ->
           if getgap lc
           then if getgap rc
                then Deleted ((Node (true, t0, d, (setgap rc false))), DLowerK)
                else (match tryLowering rc with
                      | TLtooLow -> Deleted (drot1 t0 d rc ug)
                      | TLlowered t' -> Deleted ((Node (true, t0, d, t')), DLowerK))
           else if isMissing rc
                then Deleted ((Node (true, (setgap t0 false), d, Missing)), DLowerK)
                else Deleted ((Node (ug, t0, d, rc)), DSameK))
      | DNotFound -> DNotFound)
   | CompGtT ->
     (match delete x rc with
      | Deleted dr ->
        let (t0, d0) = dr in
        (match d0 with
         | DSameK -> Deleted ((Node (ug, lc, d, t0)), DSameK)
         | DLowerK ->
           if getgap rc
           then if getgap lc
                then Deleted ((Node (true, (setgap lc false), d, t0)), DLowerK)
                else (match tryLowering lc with
                      | TLtooLow -> Deleted (drot2 lc d t0 ug)
                      | TLlowered t' -> Deleted ((Node (true, t', d, t0)), DLowerK))
           else if isMissing lc
                then Deleted ((Node (true, Missing, d, (setgap t0 false))), DLowerK)
                else Deleted ((Node (ug, lc, d, t0)), DSameK))
      | DNotFound -> DNotFound))
