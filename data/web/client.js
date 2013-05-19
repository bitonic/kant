sock = new WebSocket("ws://localhost:8000/repl");
console.log("Created socket");
log = document.getElementById("log");
sock.onopen = function () {
  log.innerHTML += "Socket open!<br>";
  log.innerHTML += "Sending data...<br>";
  sock.send(":t *");
};
sock.onmessage = function(event) {
  log.innerHTML += "Received data: " + event.data + "<br>";
};
sock.onclose = function (event) {
  log.innerHTML += "Socket close!<br>";
};
