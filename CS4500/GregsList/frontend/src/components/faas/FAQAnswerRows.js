import PropTypes from 'prop-types';
import React, { useRef, useState } from 'react';
import { Button } from 'react-bootstrap';

const FAQAnswerRows = ({ faas, onDelete, onUpdate }) => {
  const [editId, setEditId] = useState(undefined);
  const answerInputRef = useRef(undefined);

  return faas.map(faqAnswer => {
    const editing = editId === faqAnswer.id;

    return (
      <tr key={faqAnswer.id}>
        <td>{faqAnswer.frequentlyAskedQuestion.title}</td>
        <td>{faqAnswer.frequentlyAskedQuestion.question}</td>
        <td>
          {editing ? (
            <input ref={answerInputRef} defaultValue={faqAnswer.answer} />
          ) : (
            faqAnswer.answer
          )}
        </td>
        <td>
          <Button
            onClick={
              editing
                ? // Save the edits to this row
                  () => {
                    onUpdate(faqAnswer.id, {
                      answer: answerInputRef.current.value,
                    });
                    setEditId(undefined);
                  }
                : // Start editing this row
                  () => setEditId(faqAnswer.id)
            }
            size="sm"
            style={{ height: 'auto' }}
          >
            {editing ? 'Save' : 'Edit'}
          </Button>
          <Button
            onClick={() => onDelete(faqAnswer.id)}
            variant="danger"
            size="sm"
            style={{ height: 'auto' }}
          >
            X
          </Button>
        </td>
      </tr>
    );
  });
};

FAQAnswerRows.propTypes = {
  faas: PropTypes.arrayOf(
    PropTypes.shape({
      id: PropTypes.number.isRequired,
      answer: PropTypes.string.isRequired,
    }).isRequired
  ).isRequired,
};

export default FAQAnswerRows;
