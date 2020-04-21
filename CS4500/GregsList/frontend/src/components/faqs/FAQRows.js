import PropTypes from 'prop-types';
import React, { useRef, useState } from 'react';
import { Button } from 'react-bootstrap';

const FAQRows = ({ faqs, onUpdate, onDelete }) => {
  const [editId, setEditId] = useState(undefined);
  const titleInputRef = useRef(undefined);
  const questionInputRef = useRef(undefined);

  return faqs.map(faq => {
    const editing = editId === faq.id;
    return (
      <tr key={faq.id}>
        <td>
          {editing ? (
            <input ref={titleInputRef} defaultValue={faq.title} />
          ) : (
            faq.title
          )}
        </td>
        <td>
          {editing ? (
            <input ref={questionInputRef} defaultValue={faq.question} />
          ) : (
            faq.question
          )}
        </td>
        <td>
          <Button
            onClick={
              editing
                ? // Save the edits to this row
                  () => {
                    onUpdate(faq.id, {
                      title: titleInputRef.current.value,
                      question: questionInputRef.current.value,
                    });
                    setEditId(undefined);
                  }
                : // Start editing this row
                  () => setEditId(faq.id)
            }
            size="sm"
            style={{ height: 'auto' }}
          >
            {editing ? 'Save' : 'Edit'}
          </Button>
        </td>
        <td>
          <Button
            onClick={() => onDelete(faq.id)}
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

FAQRows.propTypes = {
  faqs: PropTypes.arrayOf(
    PropTypes.shape({
      id: PropTypes.number.isRequired,
      title: PropTypes.string.isRequired,
      question: PropTypes.string.isRequired,
    }).isRequired
  ).isRequired,
  onUpdate: PropTypes.func.isRequired,
  onDelete: PropTypes.func.isRequired,
};

export default FAQRows;
