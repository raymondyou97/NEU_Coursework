import React from 'react';
import { useState } from 'react';

const ServiceTrueFalseQuestion = ({ question, answer }) => {
  const [radioTrue, setRadioTrue] = useState(answer.trueFalseAnswer);

  return (
    <div>
      <h5>{question.question}</h5>
      <div>
        <label>
          <input
            name={question.question}
            type="radio"
            checked={radioTrue}
            onChange={() => setRadioTrue(true)}
          />
          Yes &nbsp;
        </label>
        <label>
          <input
            name={question.question}
            type="radio"
            checked={!radioTrue}
            onChange={() => setRadioTrue(false)}
          />
          No &nbsp;
        </label>
      </div>
      <br />
    </div>
  );
};

export default ServiceTrueFalseQuestion;
