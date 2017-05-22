from flask import Flask
import json
from flask import request
from flask import render_template
import resource_envelope

app = Flask(__name__)

@app.route('/')
def index():
    return render_template('index.html')

@app.route("/compute", methods=['POST'])
def graph_changed():
    graph = request.form["graph"]
    return json.dumps(resource_envelope.run(json.loads(graph)))

if __name__ == "__main__":
    app.run(debug=True)