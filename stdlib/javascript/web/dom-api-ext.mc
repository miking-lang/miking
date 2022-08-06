
type Location = {
  host: String,
  hostname: String,
  href: String,
  origin: String,
  pathname: String,
  port: String,
  protocol: String,
  search: String,
  reload: () -> (),
  replace: () -> (),
  assign: () -> ()
}

type Document = {
  location: Location
}

external getDocument ! : () -> Document
