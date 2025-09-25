

let () = 
    Dream.run
    @@ Dream.logger
    @@ Dream.router [
        Dream.get "/" (fun _ -> Dream.html "Hello, Double-Checkk!");
        Dream.get "/health" (fun _ -> Dream.json "{\"status\": \"ok\"}");
    ]

