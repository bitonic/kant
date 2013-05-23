// Communicates with the server specified in `kant-web.hs', which is basically a
// Kant REPL behind a websockets proxy.

// Where the past commands/responses go
var log    = document.getElementById("log");
// The <form>
var prompt = document.getElementById("prompt");
// The actual <input>
var input  = document.getElementById("input");
// The container <div>
var left   = document.getElementById("left");

var sock = new WebSocket(
  "ws://" + window.location.hostname + ":" + window.location.port + "/repl");

// Shows the input prompt
function scrollToBottom() {
  left.scrollTop = input.offsetTop;
}

// Shows something in the log
function logSpan(s, class_) {
  var sp = document.createElement('span');
  if (class_) {
    sp.setAttribute('class', class_);
  }
  sp.innerHTML = s + "\n";
  return sp;
}

// We setup the prompt machinery (history and sending stuff) in this closure, to
// keep the history data private.  Returns an event handler for a websocket
// recv.
var processInput = (function () {
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

  var sendInput = function () {
    var s = input.value;
    log.appendChild(logSpan(">>> " + s));
    scrollToBottom();
    input.value = "";
    sock.send(s);
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
  prompt.onsubmit = processInput;
};

// Receive messages of the type {status: 'ok' + 'error', body: String}.  See
// also `kant-web.hs'.
sock.onmessage = function (event) {
  var resp = JSON.parse(event.data);
  var s = escapeHtml(resp.body);
  if (!onlyWhiteSpace(s)) {
    log.appendChild(logSpan(s, resp.status === "ok" ? "response" : "error"));
    scrollToBottom();
  }
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
