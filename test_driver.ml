
open Tests ;;

let tests = [
  "0a", error0a_;
  "0b", error0b_;
  "0c", error0c_;
  "0d", error0d_;
  "1a", error1a_;
  "1b", error1b_;
  "1c", error1c_;
  "2a", error2a_;
  "2b", error2b_;
  "2c", error2c_;
  "2d", error2d_;
  "3a", error3a_;
  "3b", error3b_;
  "3c", error3c_;
  "4a", error4a_;
  "4b", error4b_;
  "5a", error5a_;
  "5b", error5b_;
  "5c", error5c_;
  "5d", error5d_;
  "6a", error6a_;
  "6b", error6b_;
  "6c", error6c_
] ;;

exception Error ;;

List.iter (fun (n,t) ->
  prerr_string ("Testing " ^ n ^ " ...");
  t (fun () -> raise Error);
  prerr_newline ()
) tests ;;
