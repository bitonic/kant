var log    = document.getElementById("log");
var prompt = document.getElementById("prompt");
var input  = document.getElementById("input");

var sock = new WebSocket(
  "ws://" + window.location.hostname + ":" + window.location.port + "/repl");

console.log("Created socket");

var processInput = (function () {
  var sendInput = function () {
    var s = input.value;
    log.innerHTML += ">>> " + s + "\n";
    input.value = "";
    sock.send(s);
  };

  var history = [];
  var cursor;                   // Index in the history.
  var current;                  // What the user has typed without submitting

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

  return function (event) {
    // Don't let the form do an action (e.g. refresh page)
    event.preventDefault();
    if (!onlyWhiteSpace(input.value)) {
      // Prevent commands being sent until this one is received
      prompt.className = "waiting";
      prompt.onsubmit = function (event) {
        event.preventDefault();
      };
      recordInput();
      sendInput();
    }
  };
})();

sock.onopen = function () {
  console.log("Socket open");
  prompt.onsubmit = processInput;
};

sock.onmessage = function (event) {
  var resp = JSON.parse(event.data);
  var s = escapeHtml(resp.body);
  if (!onlyWhiteSpace(s)) {
    log.appendChild(logSpan(s, resp.status === "ok" ? "response" : "error"));
  }
  // Show the input prompt
  input.scrollIntoView();
  // Re-allow sending of commands
  prompt.onsubmit = processInput;
  prompt.className = "active";
};

sock.onclose = function (event) {
  prompt.innerHTML = "";
  var err = "Websocket error, code " + event.code +
            (event.reason ? (", reason: " + event.reason) : "") + ".";
  prompt.appendChild(logSpan(err, "error"));
};

function logSpan(s, class_) {
  var sp = document.createElement('span');
  if (class_) {
    sp.setAttribute('class', class_);
  }
  sp.innerHTML = s + "\n";
  return sp;
}

// Utils

function escapeHtml(unsafe) {
  return unsafe.replace(/&/g, "&amp;")
               .replace(/</g, "&lt;")
               .replace(/>/g, "&gt;")
               .replace(/"/g, "&quot;")
               .replace(/'/g, "&#039;");
}

function onlyWhiteSpace(s) {
  return s.replace(/\s+/g, "") === "";
}
