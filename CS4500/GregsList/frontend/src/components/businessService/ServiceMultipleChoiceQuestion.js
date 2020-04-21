import React from 'react';
import { useState } from 'react';

const ServiceMultipleChoiceQuestion = ({ question, answer }) => {
  const choiceMap = question.choices.split(', ').reduce((acc, choice) => {
    return {
      ...acc,
      [choice]: answer.choiceAnswer.split(', ').indexOf(choice) !== -1,
    };
  }, {});
  const [choices, setChoices] = useState(choiceMap);

  const toggleChoice = choice => {
    setChoices({ ...choices, [choice]: !choices[choice] });
  };

  return (
    <div>
      <h5>{question.question}</h5>
      {question.choices.split(', ').map((choice, index) => (
        <div key={index}>
          <label>
            <input
              name={question.question}
              type="checkbox"
              value={choice}
              onChange={() => toggleChoice(choice)}
              checked={choices[choice]}
            />
            &nbsp;
            {choice}
          </label>
        </div>
      ))}
      <br />
    </div>
  );
};

export default ServiceMultipleChoiceQuestion;
