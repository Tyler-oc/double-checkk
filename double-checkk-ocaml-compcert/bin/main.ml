open Lwt.Syntax  (* for let* *)

let () =
  Dream.run
  @@ Dream.logger
  @@ Dream.router [
    Dream.get "/" (fun _ -> Dream.html "Hello, Double-Checkk!");
    Dream.get "/health" (fun _ -> Dream.json "{\"status\": \"ok\"}");
    Dream.post "/verify" (fun request ->
      let* body = Dream.body request in
      let result = Compcert_wrapper.verify body in
      if result then
        Dream.json ~status:`OK {|{ "valid": true }|}
      else
        Dream.json ~status:`OK {|{ "valid": false }|}
    )
  ]
