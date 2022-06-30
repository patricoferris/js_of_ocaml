type _ Effect.t += Get_string : string Effect.t

let get_string () = Effect.perform Get_string

let run_with (s : string) f =
  let open Effect.Deep in
  try_with
    f
    ()
    { effc =
        (fun (type a) (e : a Effect.t) ->
          match e with
          | Get_string -> Some (fun (k : (a, string) continuation) -> continue k s)
          | _ -> None)
    }

let main () = "Hello " ^ get_string ()

let () = print_endline @@ run_with "World" main
