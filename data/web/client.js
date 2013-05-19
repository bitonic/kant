var log    = document.getElementById("log");
var prompt = document.getElementById("prompt");
var input  = document.getElementById("input");

var sock = new WebSocket("ws://localhost:8000/repl");
console.log("Created socket");

var processInput = (function () {
  var sendInput = function () {
    var s = input.value;
    log.innerHTML += ">>> " + s + "\n";
    input.value = "";
    sock.send(s);
  };

  var history = [];
  var cursor;
  var current;

  var reset = function () {
    cursor = -1;
    current = null;
  };

  reset();

  var navigateHistory = function (up) {
    if (current === null) {
      current = input.value;
    }
    if (up && cursor < history.length - 1) {
      cursor++;
      input.value = history[cursor];
    } else if (!up && cursor > -1) {
      cursor--;
      if (cursor === -1) {
        input.value = current;
      } else {
        input.value = history[cursor];
      }
    }
  };

  var recordInput = function() {
    history.unshift(input.value);
    reset();
  };

  input.onkeydown = function (event) {
    var keyCode = ('which' in event) ? event.which : event.keyCode;
    if (keyCode === 38 || keyCode === 40) {
      event.preventDefault();
    }
    if (keyCode === 38) {
      navigateHistory(true);
    }
    if (keyCode === 40) {
      navigateHistory(false);
    }
  };

  return function () {
    recordInput();
    sendInput();
  };
})();

sock.onopen = function () {
  console.log("Socket open");
  prompt.onsubmit = processInput;
};

sock.onmessage = function(event) {
  var resp = JSON.parse(event.data);
  var s = escapeHtml(resp.body);
  var class_ = (resp.status === "ok") ? "response" : "error";
  if (s.replace(/\s+/g, "") !== "") {
    log.innerHTML += '<span class="' + class_ + '">' + s + '\n</span>';
  }
};

// Utils

function escapeHtml(unsafe) {
  return unsafe.replace(/&/g, "&amp;")
               .replace(/</g, "&lt;")
               .replace(/>/g, "&gt;")
               .replace(/"/g, "&quot;")
               .replace(/'/g, "&#039;");
}
