open Lwt.Syntax
open Cohttp_lwt_unix

let server_handler conn req body =
    let* body_str = Cohttp_lwt.Body.to_string body in
    Printf.eprintf "Received request body: %s\n" body_str;
    Server.respond_string ~status:`OK ~body:"Hello from OCaml server!" ()

let () =
    let port = 8080 in
    let server = Server.make ~callback:server_handler () in
    let host = Unix.inet_addr_loopback in
    let listen_address = Unix.ADDR_INET (host, port) in
    Lwt_main.run (Server.create ~mode:(`TCP listen_address) server)