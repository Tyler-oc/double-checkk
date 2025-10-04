Open Dream
Open commpcert_wrapper

let () = 
    Dream.run
    @@ Dream.logger
    @@ Dream.router [
        Dream.get "/" (fun _ -> Dream.html "Hello, Double-Checkk!");
        Dream.get "/health" (fun _ -> Dream.json "{\"status\": \"ok\"}");
        Dream.post "/verify" (fun request ->
            request |> Dream.body
            >|= (fun body -> body)
            >>= fun code ->
                let result = My_compcert_wrapper.verify code in
                if result then
                Dream.json ~status:`OK {|{ "valid": true }|}
                else
                Dream.json ~status:`OK {|{ "valid": false }|}
        )
    ]
