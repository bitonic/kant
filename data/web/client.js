var log    = document.getElementById("log");
var prompt = document.getElementById("prompt");
var input  = document.getElementById("input");

var sock = new WebSocket("ws://localhost:8000/repl");
console.log("Created socket");

function processInput() {
  var s = input.value;
  log.innerHTML += ">>> " + s + "\n";
  input.value = "";
  sock.send(s);
}

sock.onopen = function () {
  console.log("Socket open");
  prompt.onsubmit = processInput;
};

sock.onmessage = function(event) {
  var resp = JSON.parse(event.data);
  var s = resp.body;
  if (s.replace(/\s+/g, "") !== "") {
    if (resp.status === "error") {
      s = '<span class="error">' + s + '</span>';
    }
    log.innerHTML += s + "\n";
  }
};
