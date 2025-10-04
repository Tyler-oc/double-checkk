open Lwt.Syntax  (* for let* *)

let () =
  Dream.run
  @@ Dream.logger
  @@ Dream.router [
    Dream.get "/" (fun _ -> Dream.html "Hello, Double-Checkk!");
    Dream.get "/health" (fun _ -> Dream.json "{\"status\": \"ok\"}");
    Dream.post "/verify-compcert" (fun request ->
      let* body = Dream.body request in
      let compiles = Compcert_wrapper.verify body in
      if compiles then
        Dream.json ~status:`OK {|{ "compiles": true }|}
      else
        Dream.json ~status:`OK {|{ "compiles": false }|}
    )
    Dream.post "/verify-frama-c" (fun request ->
      let* body = Dream.body request in
      let result, valid = Frama_c_wrapper.verify body in
      if valid then
        Dream.json ~status:`OK {|{ "valid": true, "result": result }|}
      else
        Dream.json ~status:`OK {|{ "valid": false, "result": result }|}
    )
  ]
